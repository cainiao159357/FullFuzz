/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - test case minimizer
   ----------------------------------------

   Written and maintained by Michal Zalewski <lcamtuf@google.com>

   A simple test case minimizer that takes an input file and tries to remove
   as much data as possible while keeping the binary in a crashing state
   *or* producing consistent instrumentation output (the mode is auto-selected
   based on the initially observed behavior).
*/

#define AFL_MAIN
#include "android-ashmem.h"

#include "config.h"
#include "types.h"
#include "debug.h"
#include "alloc-inl.h"
#include "hash.h"

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <signal.h>
#include <dirent.h>
#include <fcntl.h>

#include <sys/wait.h>
#include <sys/time.h>
#include <sys/shm.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/resource.h>

static s32 child_pid;                 /* PID of the tested program         */

static u8 *trace_bits,                /* SHM with instrumentation bitmap   */
          *mask_bitmap;               /* Mask for trace bits (-B)          */

static u8 *in_file,                   /* Minimizer input test case         */
          *out_file,                  /* Minimizer output file             */
          *prog_in,                   /* Targeted program input file       */
          *target_path,               /* Path to target binary             */
          *doc_path;                  /* Path to docs                      */

static u8* in_data;                   /* Input data for trimming           */

static u32 in_len,                    /* Input data length                 */
           orig_cksum,                /* Original checksum                 */
           total_execs,               /* Total number of execs             */
           missed_hangs,              /* Misses due to hangs               */
           missed_crashes,            /* Misses due to crashes             */
           missed_paths,              /* Misses due to exec path diffs     */
           exec_tmout = EXEC_TIMEOUT; /* Exec timeout (ms)                 */

static u64 mem_limit = MEM_LIMIT;     /* Memory limit (MB)                 */

static s32 shm_id,                    /* ID of the SHM region              */
           dev_null_fd = -1;          /* FD to /dev/null                   */

static u8  crash_mode,                /* Crash-centric mode?               */
           exit_crash,                /* Treat non-zero exit as crash?     */
           edges_only,                /* Ignore hit counts?                */
           exact_mode,                /* Require path match for crashes?   */
           use_stdin = 1;             /* Use stdin for program input?      */

static volatile u8
           stop_soon,                 /* Ctrl-C pressed?                   */
           child_timed_out;           /* Child timed out?                  */


/* Classify tuple counts. This is a slow & naive version, but good enough here. */
//如白皮书所言的八个hit桶
static const u8 count_class_lookup[256] = {

  [0]           = 0,
  [1]           = 1,
  [2]           = 2,
  [3]           = 4,
  [4 ... 7]     = 8,
  [8 ... 15]    = 16,
  [16 ... 31]   = 32,
  [32 ... 127]  = 64,
  [128 ... 255] = 128

};

static void classify_counts(u8* mem) {

  u32 i = MAP_SIZE;

  if (edges_only) {

    while (i--) {
      if (*mem) *mem = 1;
      mem++;
    }

  } else {

    while (i--) {
      *mem = count_class_lookup[*mem];
      mem++;
    }

  }

}


/* Apply mask to classified bitmap (if set). */

static void apply_mask(u32* mem, u32* mask) {

  u32 i = (MAP_SIZE >> 2);

  if (!mask) return;

  while (i--) {
//取反且按位与，这样mask中本来为1的会把mem对应位清零，本来为0的不会对mem对应位产生影响
    *mem &= ~*mask;
    mem++;
    mask++;

  }

}


/* See if any bytes are set in the bitmap. */

static inline u8 anything_set(void) {

  u32* ptr = (u32*)trace_bits;
  u32  i   = (MAP_SIZE >> 2);

  while (i--) if (*(ptr++)) return 1;

  return 0;

}



/* Get rid of shared memory and temp files (atexit handler). */

static void remove_shm(void) {
//删除符号链接
  if (prog_in) unlink(prog_in); /* Ignore errors */
  //删除共享内存段
  shmctl(shm_id, IPC_RMID, NULL);

}


/* Configure shared memory. */

static void setup_shm(void) {

  u8* shm_str;
//设置大小为MAP_SIZE的共享内存段，并设置权限为可读写，返回共享内存段的id
  shm_id = shmget(IPC_PRIVATE, MAP_SIZE, IPC_CREAT | IPC_EXCL | 0600);

  if (shm_id < 0) PFATAL("shmget() failed");
//注册退出时的清理函数
  atexit(remove_shm);

  shm_str = alloc_printf("%d", shm_id);
//设置环境变量
  setenv(SHM_ENV_VAR, shm_str, 1);

  ck_free(shm_str);
//得到共享内存段的地址
  trace_bits = shmat(shm_id, NULL, 0);
  
  if (trace_bits == (void *)-1) PFATAL("shmat() failed");

}


/* Read initial file. */

static void read_initial_file(void) {

  struct stat st;
  s32 fd = open(in_file, O_RDONLY);

  if (fd < 0) PFATAL("Unable to open '%s'", in_file);

  if (fstat(fd, &st) || !st.st_size)
    FATAL("Zero-sized input file.");

  if (st.st_size >= TMIN_MAX_FILE)
    FATAL("Input file is too large (%u MB max)", TMIN_MAX_FILE / 1024 / 1024);

  in_len  = st.st_size;
  in_data = ck_alloc_nozero(in_len);

  ck_read(fd, in_data, in_len, in_file);

  close(fd);

  OKF("Read %u byte%s from '%s'.", in_len, in_len == 1 ? "" : "s", in_file);

}


/* Write output file. */

static s32 write_to_file(u8* path, u8* mem, u32 len) {

  s32 ret;

  unlink(path); /* Ignore errors */

  ret = open(path, O_RDWR | O_CREAT | O_EXCL, 0600);

  if (ret < 0) PFATAL("Unable to create '%s'", path);

  ck_write(ret, mem, len, path);

  lseek(ret, 0, SEEK_SET);

  return ret;

}


/* Handle timeout signal. */

static void handle_timeout(int sig) {

  child_timed_out = 1;
  if (child_pid > 0) kill(child_pid, SIGKILL);

}


/* Execute target application. Returns 0 if the changes are a dud, or
   1 if they should be kept. */

static u8 run_target(char** argv, u8* mem, u32 len, u8 first_run) {

  static struct itimerval it;
  int status = 0;

  s32 prog_in_fd;
  u32 cksum;

  memset(trace_bits, 0, MAP_SIZE);
  MEM_BARRIER();

  prog_in_fd = write_to_file(prog_in, mem, len);

  child_pid = fork();

  if (child_pid < 0) PFATAL("fork() failed");

  if (!child_pid) {

    struct rlimit r;
//使用dup2可以重定位文件描述符
    if (dup2(use_stdin ? prog_in_fd : dev_null_fd, 0) < 0 ||
        dup2(dev_null_fd, 1) < 0 ||
        dup2(dev_null_fd, 2) < 0) {

      *(u32*)trace_bits = EXEC_FAIL_SIG;
      PFATAL("dup2() failed");

    }

    close(dev_null_fd);
    close(prog_in_fd);

    setsid();
//设置内存限制
    if (mem_limit) {

      r.rlim_max = r.rlim_cur = ((rlim_t)mem_limit) << 20;

#ifdef RLIMIT_AS

      setrlimit(RLIMIT_AS, &r); /* Ignore errors */

#else

      setrlimit(RLIMIT_DATA, &r); /* Ignore errors */

#endif /* ^RLIMIT_AS */

    }
//限制资源使用
    r.rlim_max = r.rlim_cur = 0;
    setrlimit(RLIMIT_CORE, &r); /* Ignore errors */
//执行目标程序
    execv(target_path, argv);

    *(u32*)trace_bits = EXEC_FAIL_SIG;
    exit(0);

  }

  close(prog_in_fd);

  /* Configure timeout, wait for child, cancel timeout. */
//开始计时器
  child_timed_out = 0;
  it.it_value.tv_sec = (exec_tmout / 1000);
  it.it_value.tv_usec = (exec_tmout % 1000) * 1000;

  setitimer(ITIMER_REAL, &it, NULL);

  if (waitpid(child_pid, &status, 0) <= 0) FATAL("waitpid() failed");
//停止计时器
  child_pid = 0;
  it.it_value.tv_sec = 0;
  it.it_value.tv_usec = 0;

  setitimer(ITIMER_REAL, &it, NULL);

  MEM_BARRIER();

  /* Clean up bitmap, analyze exit condition, etc. */

  if (*(u32*)trace_bits == EXEC_FAIL_SIG)
    FATAL("Unable to execute '%s'", argv[0]);
//查看共享内存区域
  classify_counts(trace_bits);
  //设置mask
  apply_mask((u32*)trace_bits, (u32*)mask_bitmap);
  total_execs++;

  if (stop_soon) {
//如果退出的话本进程页退出
    SAYF(cRST cLRD "\n+++ Minimization aborted by user +++\n" cRST);
    close(write_to_file(out_file, in_data, in_len));
    exit(1);

  }

  /* Always discard inputs that time out. */

  if (child_timed_out) {

    missed_hangs++;
    return 0;

  }

  /* Handle crashing inputs depending on current mode. */

  if (WIFSIGNALED(status) ||
      (WIFEXITED(status) && WEXITSTATUS(status) == MSAN_ERROR) ||
      (WIFEXITED(status) && WEXITSTATUS(status) && exit_crash)) {
//触发了crash
    if (first_run) crash_mode = 1;

    if (crash_mode) {
//// 如果是 crash mode，且不要求 crash 路径与原 input 相同，则立即报告 input 有效，该保留
      if (!exact_mode) return 1;

    } else {
// 是 non-crash mode，但现在 crash 了，说明这个 input 与原 input 路径不同，该丢弃
      missed_crashes++;
      return 0;

    }

  } else

  /* Handle non-crashing inputs appropriately. */

  if (crash_mode) {
//丢失覆盖度
    missed_paths++;
    return 0;

  }
//注意这里的 shm 已经是 hit count 分桶处理之后的了
  cksum = hash32(trace_bits, MAP_SIZE, HASH_CONST);

  if (first_run) orig_cksum = cksum;

  if (orig_cksum == cksum) return 1;
    //丢失覆盖度
  missed_paths++;
  return 0;

}


/* Find first power of two greater or equal to val. */
//找到大于或者等于val的2的指数
static u32 next_p2(u32 val) {

  u32 ret = 1;
  while (val > ret) ret <<= 1;
  return ret;

}


/* Actually minimize! */

static void minimize(char** argv) {

  static u32 alpha_map[256];

  u8* tmp_buf = ck_alloc_nozero(in_len);
  u32 orig_len = in_len, stage_o_len;

  u32 del_len, set_len, del_pos, set_pos, i, alpha_size, cur_pass = 0;
  u32 syms_removed, alpha_del0 = 0, alpha_del1, alpha_del2, alpha_d_total = 0;
  u8  changed_any, prev_del;

//块规范化,找到内容不敏感的内存并替换成字符'0',有利于后面的优化
  /***********************
   * BLOCK NORMALIZATION *
   ***********************/

  set_len    = next_p2(in_len / TMIN_SET_STEPS);
  set_pos    = 0;
//判断是否小于最小的size
  if (set_len < TMIN_SET_MIN_SIZE) set_len = TMIN_SET_MIN_SIZE;

  ACTF(cBRI "Stage #0: " cRST "One-time block normalization...");

  while (set_pos < in_len) {

    u8  res;
    u32 use_len = MIN(set_len, in_len - set_pos);
//检查有没有等于'0'的，如果全为'0'才会使i=use_len,但凡有一个不等于'0'都会使i!=use_len
    for (i = 0; i < use_len; i++)
      if (in_data[set_pos + i] != '0') break;

    if (i != use_len) {

      memcpy(tmp_buf, in_data, in_len);
      //但凡有一个不等于'0',都会全部设置为0
      memset(tmp_buf + set_pos, '0', use_len);
  
      res = run_target(argv, tmp_buf, in_len, 0);

      if (res) {
//res=1则代表输入有效，直接把in_data相对应的地方设置为'0'，如果res=0则代表无效，就不会修改in_data
        memset(in_data + set_pos, '0', use_len);
        changed_any = 1;
        alpha_del0 += use_len;

      }

    }

    set_pos += set_len;

  }

  alpha_d_total += alpha_del0;

  OKF("Block normalization complete, %u byte%s replaced.", alpha_del0,
      alpha_del0 == 1 ? "" : "s");

next_pass:

  ACTF(cYEL "--- " cBRI "Pass #%u " cYEL "---", ++cur_pass);
  changed_any = 0;

  /******************
   * BLOCK DELETION *
   ******************/
//把输入内容分成16块
  del_len = next_p2(in_len / TRIM_START_STEPS);
  stage_o_len = in_len;

  ACTF(cBRI "Stage #1: " cRST "Removing blocks of data...");
//一直缩小块，直到del_len=1
next_del_blksize:

  if (!del_len) del_len = 1;
  del_pos  = 0;
  prev_del = 1;

  SAYF(cGRA "    Block length = %u, remaining size = %u\n" cRST,
       del_len, in_len);

  while (del_pos < in_len) {

    u8  res;
    s32 tail_len;

    tail_len = in_len - del_pos - del_len;
    if (tail_len < 0) tail_len = 0;

    /* If we have processed at least one full block (initially, prev_del == 1),
       and we did so without deleting the previous one, and we aren't at the
       very end of the buffer (tail_len > 0), and the current block is the same
       as the previous one... skip this step as a no-op. */

    if (!prev_del && tail_len && !memcmp(in_data + del_pos - del_len,
        in_data + del_pos, del_len)) {

      del_pos += del_len;
      continue;

    }

    prev_del = 0;

    /* Head */
    memcpy(tmp_buf, in_data, del_pos);

    /* Tail */
    //删去了从del_pos开始del_len大小的块
    memcpy(tmp_buf + del_pos, in_data + del_pos + del_len, tail_len);

    res = run_target(argv, tmp_buf, del_pos + tail_len, 0);

    if (res) {
//代表删去的输入对覆盖度没有用。更新in_data和in_len
      memcpy(in_data, tmp_buf, del_pos + tail_len);
      prev_del = 1;
      in_len   = del_pos + tail_len;

      changed_any = 1;

    } else del_pos += del_len;

  }
//如果还能缩小则把del_len除以2继续精简输入
  if (del_len > 1 && in_len >= 1) {

    del_len /= 2;
    goto next_del_blksize;

  }

  OKF("Block removal complete, %u bytes deleted.", stage_o_len - in_len);

  if (!in_len && changed_any)
    WARNF(cLRD "Down to zero bytes - check the command line and mem limit!" cRST);

  if (cur_pass > 1 && !changed_any) goto finalize_all;

  /*************************
   * ALPHABET MINIMIZATION *
   *************************/

  alpha_size   = 0;
  alpha_del1   = 0;
  syms_removed = 0;

  memset(alpha_map, 0, 256 * sizeof(u32));
//使用一个map记录各个字符使用情况
  for (i = 0; i < in_len; i++) {
    if (!alpha_map[in_data[i]]) alpha_size++;
    alpha_map[in_data[i]]++;
  }

  ACTF(cBRI "Stage #2: " cRST "Minimizing symbols (%u code point%s)...",
       alpha_size, alpha_size == 1 ? "" : "s");
//遍历每个字符
  for (i = 0; i < 256; i++) {

    u32 r;
    u8 res;
//如果是等于'0'或者没记录过的字符则直接循环到下一个字符
    if (i == '0' || !alpha_map[i]) continue;

    memcpy(tmp_buf, in_data, in_len);
//把当前字符修改成'0'
    for (r = 0; r < in_len; r++)
      if (tmp_buf[r] == i) tmp_buf[r] = '0'; 

    res = run_target(argv, tmp_buf, in_len, 0);

    if (res) {

      memcpy(in_data, tmp_buf, in_len);
      //无效符号加一，即删除了一个字符
      syms_removed++;
      alpha_del1 += alpha_map[i];
      changed_any = 1;

    }

  }

  alpha_d_total += alpha_del1;

  OKF("Symbol minimization finished, %u symbol%s (%u byte%s) replaced.",
      syms_removed, syms_removed == 1 ? "" : "s",
      alpha_del1, alpha_del1 == 1 ? "" : "s");

  /**************************
   * CHARACTER MINIMIZATION *
   **************************/

  alpha_del2 = 0;

  ACTF(cBRI "Stage #3: " cRST "Character minimization...");

  memcpy(tmp_buf, in_data, in_len);
//继续把无关字符格式化为'0'
  for (i = 0; i < in_len; i++) {

    u8 res, orig = tmp_buf[i];

    if (orig == '0') continue;
    tmp_buf[i] = '0';

    res = run_target(argv, tmp_buf, in_len, 0);

    if (res) {

      in_data[i] = '0';
      alpha_del2++;
      changed_any = 1;

    } else tmp_buf[i] = orig;

  }

  alpha_d_total += alpha_del2;

  OKF("Character minimization done, %u byte%s replaced.",
      alpha_del2, alpha_del2 == 1 ? "" : "s");
//如果这这一轮中有修改输入则再进行一轮
  if (changed_any) goto next_pass;

finalize_all:

  SAYF("\n"
       cGRA "     File size reduced by : " cRST "%0.02f%% (to %u byte%s)\n"
       cGRA "    Characters simplified : " cRST "%0.02f%%\n"
       cGRA "     Number of execs done : " cRST "%u\n"
       cGRA "          Fruitless execs : " cRST "path=%u crash=%u hang=%s%u\n\n",
       100 - ((double)in_len) * 100 / orig_len, in_len, in_len == 1 ? "" : "s",
       ((double)(alpha_d_total)) * 100 / (in_len ? in_len : 1),
       total_execs, missed_paths, missed_crashes, missed_hangs ? cLRD : "",
       missed_hangs);

  if (total_execs > 50 && missed_hangs * 10 > total_execs)
    WARNF(cLRD "Frequent timeouts - results may be skewed." cRST);

}



/* Handle Ctrl-C and the like. */

static void handle_stop_sig(int sig) {

  stop_soon = 1;

  if (child_pid > 0) kill(child_pid, SIGKILL);

}


/* Do basic preparations - persistent fds, filenames, etc. */

static void set_up_environment(void) {

  u8* x;

  dev_null_fd = open("/dev/null", O_RDWR);
  if (dev_null_fd < 0) PFATAL("Unable to open /dev/null");

  if (!prog_in) {

    u8* use_dir = ".";

    if (access(use_dir, R_OK | W_OK | X_OK)) {

      use_dir = getenv("TMPDIR");
      if (!use_dir) use_dir = "/tmp";

    }

    prog_in = alloc_printf("%s/.afl-tmin-temp-%u", use_dir, getpid());

  }

  /* Set sane defaults... */

  x = getenv("ASAN_OPTIONS");

  if (x) {

    if (!strstr(x, "abort_on_error=1"))
      FATAL("Custom ASAN_OPTIONS set without abort_on_error=1 - please fix!");

    if (!strstr(x, "symbolize=0"))
      FATAL("Custom ASAN_OPTIONS set without symbolize=0 - please fix!");

  }

  x = getenv("MSAN_OPTIONS");

  if (x) {

    if (!strstr(x, "exit_code=" STRINGIFY(MSAN_ERROR)))
      FATAL("Custom MSAN_OPTIONS set without exit_code="
            STRINGIFY(MSAN_ERROR) " - please fix!");

    if (!strstr(x, "symbolize=0"))
      FATAL("Custom MSAN_OPTIONS set without symbolize=0 - please fix!");

  }

  setenv("ASAN_OPTIONS", "abort_on_error=1:"
                         "detect_leaks=0:"
                         "symbolize=0:"
                         "allocator_may_return_null=1", 0);

  setenv("MSAN_OPTIONS", "exit_code=" STRINGIFY(MSAN_ERROR) ":"
                         "symbolize=0:"
                         "abort_on_error=1:"
                         "allocator_may_return_null=1:"
                         "msan_track_origins=0", 0);

  if (getenv("AFL_PRELOAD")) {
    setenv("LD_PRELOAD", getenv("AFL_PRELOAD"), 1);
    setenv("DYLD_INSERT_LIBRARIES", getenv("AFL_PRELOAD"), 1);
  }

}


/* Setup signal handlers, duh. */

static void setup_signal_handlers(void) {

  struct sigaction sa;

  sa.sa_handler   = NULL;
  sa.sa_flags     = SA_RESTART;
  sa.sa_sigaction = NULL;

  sigemptyset(&sa.sa_mask);

  /* Various ways of saying "stop". */
//杀死子进程
  sa.sa_handler = handle_stop_sig;
  sigaction(SIGHUP, &sa, NULL);
  sigaction(SIGINT, &sa, NULL);//ctrl+c
  sigaction(SIGTERM, &sa, NULL);

  /* Exec timeout notifications. */
//杀死子进程
  sa.sa_handler = handle_timeout;
  sigaction(SIGALRM, &sa, NULL);

}


/* Detect @@ in args. */

static void detect_file_args(char** argv) {

  u32 i = 0;
  u8* cwd = getcwd(NULL, 0);

  if (!cwd) PFATAL("getcwd() failed");

  while (argv[i]) {
//用于目标程序从文件中读取
    u8* aa_loc = strstr(argv[i], "@@");

    if (aa_loc) {

      u8 *aa_subst, *n_arg;

      /* Be sure that we're always using fully-qualified paths. */
//获得输入文件的绝对路径
      if (prog_in[0] == '/') aa_subst = prog_in;
      else aa_subst = alloc_printf("%s/%s", cwd, prog_in);

      /* Construct a replacement argv value. */

      //使用aa_loc操作了argv[i]，因此，argv[i][0]=0
      *aa_loc = 0;
      n_arg = alloc_printf("%s%s%s", argv[i], aa_subst, aa_loc + 2);
      argv[i] = n_arg;
      *aa_loc = '@';
      if (prog_in[0] != '/') ck_free(aa_subst);

    }

    i++;

  }

  free(cwd); /* not tracked */

}


/* Display usage hints. */

static void usage(u8* argv0) {

  SAYF("\n%s [ options ] -- /path/to/target_app [ ... ]\n\n"

       "Required parameters:\n\n"

       "  -i file       - input test case to be shrunk by the tool\n"
       "  -o file       - final output location for the minimized data\n\n"

       "Execution control settings:\n\n"

       "  -f file       - input file read by the tested program (stdin)\n"
       "  -t msec       - timeout for each run (%u ms)\n"
       "  -m megs       - memory limit for child process (%u MB)\n"
       "  -Q            - use binary-only instrumentation (QEMU mode)\n\n"

       "Minimization settings:\n\n"

       "  -e            - solve for edge coverage only, ignore hit counts\n"
       "  -x            - treat non-zero exit codes as crashes\n\n"

       "Other stuff:\n\n"

       "  -V            - show version number and exit\n\n"

       "For additional tips, please consult %s/README.\n\n",

       argv0, EXEC_TIMEOUT, MEM_LIMIT, doc_path);

  exit(1);

}


/* Find binary. */

static void find_binary(u8* fname) {

  u8* env_path = 0;
  struct stat st;
//有/符号代表是确定路径，如果没有则去环境变量中找
  if (strchr(fname, '/') || !(env_path = getenv("PATH"))) {

    target_path = ck_strdup(fname);
    //获取目标文件且检查文件属性
    if (stat(target_path, &st) || !S_ISREG(st.st_mode) ||
        !(st.st_mode & 0111) || st.st_size < 4)
      FATAL("Program '%s' not found or not executable", fname);

  } else {
//遍历PATH中的每一个路径，找到fname文件
    while (env_path) {

      u8 *cur_elem, *delim = strchr(env_path, ':');

      if (delim) {

        cur_elem = ck_alloc(delim - env_path + 1);
        memcpy(cur_elem, env_path, delim - env_path);
        delim++;

      } else cur_elem = ck_strdup(env_path);

      env_path = delim;

      if (cur_elem[0])
        target_path = alloc_printf("%s/%s", cur_elem, fname);
      else
        target_path = ck_strdup(fname);

      ck_free(cur_elem);

      if (!stat(target_path, &st) && S_ISREG(st.st_mode) &&
          (st.st_mode & 0111) && st.st_size >= 4) break;

      ck_free(target_path);
      target_path = 0;

    }

    if (!target_path) FATAL("Program '%s' not found or not executable", fname);

  }

}


/* Fix up argv for QEMU. */

static char** get_qemu_argv(u8* own_loc, char** argv, int argc) {

  char** new_argv = ck_alloc(sizeof(char*) * (argc + 4));
  u8 *tmp, *cp, *rsl, *own_copy;

  /* Workaround for a QEMU stability glitch. */

  setenv("QEMU_LOG", "nochain", 1);

  memcpy(new_argv + 3, argv + 1, sizeof(char*) * argc);

  /* Now we need to actually find qemu for argv[0]. */

  new_argv[2] = target_path;
  new_argv[1] = "--";

  tmp = getenv("AFL_PATH");

  if (tmp) {

    cp = alloc_printf("%s/afl-qemu-trace", tmp);

    if (access(cp, X_OK))
      FATAL("Unable to find '%s'", tmp);

    target_path = new_argv[0] = cp;
    return new_argv;

  }

  own_copy = ck_strdup(own_loc);
  rsl = strrchr(own_copy, '/');

  if (rsl) {

    *rsl = 0;

    cp = alloc_printf("%s/afl-qemu-trace", own_copy);
    ck_free(own_copy);

    if (!access(cp, X_OK)) {

      target_path = new_argv[0] = cp;
      return new_argv;

    }

  } else ck_free(own_copy);

  if (!access(BIN_PATH "/afl-qemu-trace", X_OK)) {

    target_path = new_argv[0] = BIN_PATH "/afl-qemu-trace";
    return new_argv;

  }

  FATAL("Unable to find 'afl-qemu-trace'.");

}


/* Read mask bitmap from file. This is for the -B option. */

static void read_bitmap(u8* fname) {

  s32 fd = open(fname, O_RDONLY);

  if (fd < 0) PFATAL("Unable to open '%s'", fname);

  ck_read(fd, mask_bitmap, MAP_SIZE, fname);

  close(fd);

}



/* Main entry point */

int main(int argc, char** argv) {

  s32 opt;
  u8  mem_limit_given = 0, timeout_given = 0, qemu_mode = 0;
  char** use_argv;

  doc_path = access(DOC_PATH, F_OK) ? "docs" : DOC_PATH;

  SAYF(cCYA "afl-tmin " cBRI VERSION cRST " by <lcamtuf@google.com>\n");

  //使用getopt获得参数
  while ((opt = getopt(argc,argv,"+i:o:f:m:t:B:xeQV")) > 0)

    switch (opt) {

      case 'i':

        if (in_file) FATAL("Multiple -i options not supported");
        in_file = optarg;
        break;

      case 'o':

        if (out_file) FATAL("Multiple -o options not supported");
        out_file = optarg;
        break;

      case 'f':

        if (prog_in) FATAL("Multiple -f options not supported");
        use_stdin = 0;
        prog_in   = optarg;
        break;

      case 'e':

        if (edges_only) FATAL("Multiple -e options not supported");
        edges_only = 1;
        break;

      case 'x':

        if (exit_crash) FATAL("Multiple -x options not supported");
        exit_crash = 1;
        break;

      case 'm': {

          u8 suffix = 'M';

          if (mem_limit_given) FATAL("Multiple -m options not supported");
          mem_limit_given = 1;

          if (!strcmp(optarg, "none")) {
              //默认是50
            mem_limit = 0;
            break;

          }

          if (sscanf(optarg, "%llu%c", &mem_limit, &suffix) < 1 ||
              optarg[0] == '-') FATAL("Bad syntax used for -m");

          switch (suffix) {
//默认单位是MB
            case 'T': mem_limit *= 1024 * 1024; break;
            case 'G': mem_limit *= 1024; break;
            case 'k': mem_limit /= 1024; break;
            case 'M': break;

            default:  FATAL("Unsupported suffix or bad syntax for -m");

          }

          if (mem_limit < 5) FATAL("Dangerously low value of -m");

          //检查一下，不能太大
          if (sizeof(rlim_t) == 4 && mem_limit > 2000)
            FATAL("Value of -m out of range on 32-bit systems");

        }

        break;

      case 't':

        if (timeout_given) FATAL("Multiple -t options not supported");
        timeout_given = 1;

        exec_tmout = atoi(optarg);

        if (exec_tmout < 10 || optarg[0] == '-')
          FATAL("Dangerously low value of -t");

        break;

      case 'Q':

          //qemu模式
        if (qemu_mode) FATAL("Multiple -Q options not supported");
        if (!mem_limit_given) mem_limit = MEM_LIMIT_QEMU;

        qemu_mode = 1;
        break;

      case 'B': /* load bitmap */

        /* This is a secret undocumented option! It is speculated to be useful
           if you have a baseline "boring" input file and another "interesting"
           file you want to minimize.

           You can dump a binary bitmap for the boring file using
           afl-showmap -b, and then load it into afl-tmin via -B. The minimizer
           will then minimize to preserve only the edges that are unique to
           the interesting input file, but ignoring everything from the
           original map.

           The option may be extended and made more official if it proves
           to be useful. */
//当使用 -B 选项时，您提供给 afl-tmin 的是一个二进制位图文件，它描述了一个或多个已有测试用例触发目标程序的执行路径。
// afl-tmin 会尝试最小化当前测试用例，以便保留那些未被已有测试用例覆盖的执行路径。换句话说，它会删除那些已经被其他测试用例触发的路径，
// 但保留那些仍然能够触发新路径的字节。
        if (mask_bitmap) FATAL("Multiple -B options not supported");
        mask_bitmap = ck_alloc(MAP_SIZE);
        //读bitmap到mask_bitmap
        read_bitmap(optarg);
        break;

      case 'V': /* Show version number */

        /* Version number has been printed already, just quit. */
        exit(0);

      default:

        usage(argv[0]);

    }

  if (optind == argc || !in_file || !out_file) usage(argv[0]);
//初始化共享内存段
  setup_shm();
  //设置信号处理函数
  setup_signal_handlers();
//设置变量dev_null_fd和prog_in
  set_up_environment();
//找到target program
  find_binary(argv[optind]);
//处理目标程序的命令行参数，主要是处理@@参数
  detect_file_args(argv + optind);

  if (qemu_mode)
    use_argv = get_qemu_argv(argv[0], argv + optind, argc - optind);
  else
    use_argv = argv + optind;

  exact_mode = !!getenv("AFL_TMIN_EXACT");

  SAYF("\n");
//读取inputfile的内容并存储在in_data变量里
  read_initial_file();

  ACTF("Performing dry run (mem limit = %llu MB, timeout = %u ms%s)...",
       mem_limit, exec_tmout, edges_only ? ", edges only" : "");
//运行目标程序，并用返回值判断输入是否有效，如果有效则返回1，如果无效则返回0，是否有效取决于是否出在crash_mode和覆盖度是否相同
//第一次运行并且造成crash则判断为crash_mode
  run_target(use_argv, in_data, in_len, 1);

  if (child_timed_out)
    FATAL("Target binary times out (adjusting -t may help).");

  if (!crash_mode) {

     OKF("Program terminates normally, minimizing in " 
         cCYA "instrumented" cRST " mode.");
//判断有没有插桩，如果没有插桩则直接退出，总结如果是non-crash模式下且程序没有插桩则直接退出
     if (!anything_set()) FATAL("No instrumentation detected.");

  } else {

     OKF("Program exits with a signal, minimizing in " cMGN "%scrash" cRST
         " mode.", exact_mode ? "EXACT " : "");

  }
//精简输入内容
  minimize(use_argv);

  ACTF("Writing output to '%s'...", out_file);

  unlink(prog_in);
  prog_in = NULL;
//把精简过后的内容写入outfile
  close(write_to_file(out_file, in_data, in_len));

  OKF("We're done here. Have a nice day!\n");

  exit(0);

}

