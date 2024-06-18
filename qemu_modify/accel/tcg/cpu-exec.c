/*
 *  emulator main execution loop
 *
 *  Copyright (c) 2003-2005 Fabrice Bellard
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, see <http://www.gnu.org/licenses/>.
 */

int lmbench_count = 0;
int lat_select_init = 0;
extern int thread_pool;
extern int analysis_start;
extern int coroutine_start;
int stay_in_full = 0;

int start_fork_pc;
int libuclibc_addr = 0;
int not_exit = 0;
int tmp_not_exit = 0;
int last_pc = 0;
int end_pc = 0;
int program_id = 0;
int auto_find_fork_times = 0;
int poll_times = 0;
double full_store_page_time = 0.0;

int thread_context = 1;
int stack_mask = 0;
int ori_thread = 0;
int recv_times = 1;
int fork_accept_times = 1;
int accept_times = 0;
int accept_fd = 0;
int handle_recv = 0;
int count_142 = 0;
int count_3 = 0;
int sys_count = 0;

int CP0_UserLocal = 0;
int system_flag=0xdeaddead;


#include "zyw_config1.h"
#include "zyw_config2.h"
#ifdef SNAPSHOT_SYNC
char *phys_addr_stored_bitmap; 

int add_physical_page(int phys_addr)
{
    int value = phys_addr >> 12;
    int index = value >> 3;
    int position = value & 0x07;

    phys_addr_stored_bitmap[index] |=  1 << position;
}

//if not exist,add it and return -1; if exist, return index;
int if_physical_exist(int phys_addr) //phys_addr <= 0x7ffff000
{   
    int value = phys_addr >> 12;
    int index = value >> 3;
    int position = value & 0x07;
    return (phys_addr_stored_bitmap[index] & (1 << position)) !=0; 

}
#endif 


#if defined(FUZZ) || defined(MEM_MAPPING)
#include "afl-qemu-cpu-inl.h" //AFL_QEMU_CPU_SNIPPET
extern int afl_wants_cpu_to_stop;
int exit_status = 0;
int full_store_count = 0;
//int tmp_print = 0;

void getconfig(char *keywords, char *res)
{
    FILE *fp = fopen("FirmAFL_config", "r");
    char StrLine[256];
    while (!feof(fp)) 
    { 
        fgets(StrLine,256,fp);
        char * key = strtok(StrLine, "=");
        char * value = strtok(NULL, "=");
        int val_len = strlen(value);
        if(value[val_len-1] == '\n')
        {
            value[val_len-1] = '\0';
        } 
        if(strcmp(keywords, key) == 0)
        {
            strcpy(res, value);
            break;
        }
    }
    fclose(fp); 
}


#endif

#ifdef MEM_MAPPING
int pipe_read_fd = -1;
int pipe_write_fd = -1; 
int read_type = -1;
int is_loop_over = 1;
int first_time = 0; //tlb store
int syscall_request = 0;


int write_addr(uintptr_t ori_addr, uintptr_t addr);
#endif

#include "qemu/osdep.h"
#include "cpu.h"
#include "trace.h"
#include "disas/disas.h"
#include "exec/exec-all.h"
#include "tcg.h"
#include "qemu/atomic.h"
#include "sysemu/qtest.h"
#include "qemu/timer.h"
#include "exec/address-spaces.h"
#include "qemu/rcu.h"
#include "exec/tb-hash.h"
#include "exec/log.h"
#include "qemu/main-loop.h"
#if defined(TARGET_I386) && !defined(CONFIG_USER_ONLY)
#include "hw/i386/apic.h"
#endif
#include "sysemu/cpus.h"
#include "sysemu/replay.h"


#ifdef TARGET_MIPS
target_ulong kernel_base = 0x80000000;
#elif defined(TARGET_ARM)
target_ulong kernel_base = 0xc0000000;
#endif


target_ulong handle_addr;
int handle_addr_prot;
target_ulong write_vaddr = 0;
target_ulong write_paddr = 0;


#ifdef MEM_MAPPING
typedef struct MISSING_PAGE{
    target_ulong addr;
    int prot; 
    int mmu_idx;
} MISSING_PAGE;

typedef struct 
{
  double handle_state_time;
  double handle_addr_time;
  double handle_syscall_time;
  double store_page_time;
  double restore_page_time;
  int user_syscall_count;
  int user_store_count;
} USER_MODE_TIME;

MISSING_PAGE handle_page;
int ask_addr = 0;
uintptr_t res_addr;
int tcg_handle_addr = 0;

#endif 

//zyw
#ifdef TARGET_ARM
typedef struct ARMMMUFaultInfo ARMMMUFaultInfo;
struct ARMMMUFaultInfo {
    target_ulong s2addr;
    bool stage2;
    bool s1ptw;
};
#endif
#define BREAK_IF(x) if(x) break
int total_count = 10000;
int count = 0;
int tmptmptmp = 0;
int brk_end = 0;
FILE * open_log_file = NULL;


int config_pc = 0;
char program_analysis[256];
char feed_type[256];
int environ_offset = 0;
char lib_name[256];
int program_type = 0;


int FirmAFL_config()
{
    memset(feed_type, 0, 256);
    getconfig("feed_type",feed_type);
    assert(strlen(feed_type)>0);

    char fork_pc_str[256];
    memset(fork_pc_str, 0, 256);
    getconfig("start_fork_pc", fork_pc_str);
    if(strlen(fork_pc_str) > 0)
    {   
        config_pc = strtol(fork_pc_str, NULL, 16);
        assert(config_pc!=0);
    }
#ifdef FUZZ  
    if(strcmp(feed_type, "FEED_ENV") == 0)
    {
        getconfig("lib_name", lib_name);
        char offset_str[256];
        getconfig("environ_offset", offset_str);
        environ_offset = strtol(offset_str, NULL, 16);
        assert(strlen(lib_name) > 0);
        assert(environ_offset!=0);
    }
    char end_pc_str[256];
    memset(end_pc_str, 256, 0);
    getconfig("end_pc", end_pc_str);
    if(strlen(end_pc_str) > 0)
    {
        end_pc = strtol(end_pc_str, NULL, 16);
    }
#endif
    char id_str[256];
    memset(id_str, 256, 0);
    getconfig("id", id_str);
    if(strlen(id_str) > 0)
    {
        program_id = strtol(id_str, NULL, 10);
    }
    
    if(program_id == 105600)
    {
        fork_accept_times = 3;
    }
    if(program_id == 161161)
    {
        fork_accept_times = 1;
    }
    if(program_id == 11143)
    {
        fork_accept_times = 2;
    }
    // getconfig("program_analysis", program_analysis); 
    assert(strlen(program_analysis)>0);
    /*
    if(strcmp(program_analysis, "httpd") == 0 || strcmp(program_analysis, "miniupnpd") == 0)
    {
        program_type = 1;
    }
    */
    /*
    else if(strcmp(program_analysis, "network.cgi") == 0 || strcmp(program_analysis, "video.cgi") == 0)
    {
        program_type = 1;
    }
    */
}


#ifdef FUZZ

static void convert_endian_4b(uint32_t *data)
{
   *data = ((*data & 0xff000000) >> 24)
         | ((*data & 0x00ff0000) >>  8)
         | ((*data & 0x0000ff00) <<  8)
         | ((*data & 0x000000ff) << 24);
}

static void read_ptr(CPUState* cpu, int vaddr, uint32_t *pptr)
{
    cpu_memory_rw_debug(cpu, vaddr, pptr, 4, 0);
#ifdef TARGET_WORDS_BIGENDIAN
    convert_endian_4b(pptr);
#endif
}

static void write_ptr(CPUState* cpu, int vaddr, int pptr_addr)
{
#ifdef TARGET_WORDS_BIGENDIAN
    convert_endian_4b(&pptr_addr);
#endif
    cpu_memory_rw_debug(cpu, vaddr, &pptr_addr, 4, 1);

}
char * aflFile;

target_ulong getWork(char * ptr, target_ulong sz)
{
    target_ulong retsz;
    FILE *fp;
    unsigned char ch;
    //printf("pid %d: getWork %lx %lx\n", getpid(), ptr, sz);fflush(stdout);
    //printf("filename:%s\n",aflFile);
    fp = fopen(aflFile, "rb");
    if(!fp) {
        perror(aflFile);
        printf("aflfile open failed:%s\n", aflFile);
        return errno;
    }
    retsz = 0;
    while(retsz < sz) {
        if(fread(&ch, 1, 1, fp) == 0)
            break;
        //cpu_stb_data(env, ptr, ch);
        *ptr = ch;
        retsz ++;
        ptr ++;
    }
    *ptr = '\0';
    fclose(fp);
    return retsz;
}


//FEED_ENV
int replace_addr = 0;
int global_addr = 0;
int environ_addr;
int content_addr;
int pre_feed_finish = 0;

//FEED_HTTP
char http_package[50][4096];
char tmp_http_package[50][4096];
char http_key[50][100];
char http_value[50][4096];
int package_index = 0;
int feed_addr = 0;

char recv_buf[4096];
int total_len = 0;
int buf_read_index = 0;


int write_package(CPUState *cpu, int vir_addr, char* cont, int len)
{
    //DECAF_printf("write_package:%x,%x\n", vir_addr, len);
    int ret = DECAF_write_mem(cpu, vir_addr, len, cont);
    if(ret ==-1)
    {
        DECAF_printf("write failed %x,%x\n", vir_addr, len);
        sleep(1000);
    }
    else
    {
        //DECAF_printf("write %x,%x\n", vir_addr, len);
    }
    return vir_addr + len;
}


void prepare_feed_input(CPUState * cpu)
{
    CPUArchState *env = cpu->env_ptr;
    if(strcmp(feed_type, "FEED_ENV") == 0)
    {
        pre_feed_finish = 1;
        char modname[512];
        target_ulong base;
        target_ulong pgd = DECAF_getPGD(cpu);
        DECAF_printf("print_mapping for %x\n", pgd);
        FILE * fp2 = fopen("mapping", "w");
        print_mapping(modname, pgd, &base, fp2);// obtain mapping
        fclose(fp2);
        FILE * fp3 = fopen("mapping", "r");
        char strline[100];
        while(fgets(strline, 100, fp3)!=NULL)
        {
            char *p1 = strtok(strline, ":");
            char *p2 = strtok(NULL, ":");
            char *p3 = strtok(NULL, ":");
            char *p4 = strtok(NULL, ":");
            p4[strlen(p4)-1]='\0';
            if(strcmp(p4, lib_name) ==0)
            {
                int gva_start = strtol(p1,NULL, 16);
                libuclibc_addr = gva_start;
                DECAF_printf("libuclibc addr:%x\n", libuclibc_addr);
                break;
            }    
        }
        fclose(fp3);

        global_addr = libuclibc_addr + environ_offset; 


        read_ptr(cpu, global_addr, &environ_addr);
        read_ptr(cpu, environ_addr, &content_addr);
        DECAF_printf("global addr:%lx, %lx,%lx\n",global_addr, environ_addr, content_addr);
        get_page_addr_code(env, content_addr); //important
        //write_ptr(cpu, environ_addr + 4, 0);
    }
    else if(strcmp(feed_type, "FEED_HTTP") == 0)
    {

        /*
        pre_feed_finish = 1;
        CPUArchState *env= cpu->env_ptr;
#ifdef TARGET_MIPS
        feed_addr = env->active_tc.gpr[5];
#else defined(TARGET_ARM)
        feed_addr = env->regs[1];
#endif
        */
    }
    else if (strcmp(feed_type, "FEED_CMD") == 0)
    {
        CPUArchState *env = cpu->env_ptr;
#ifdef TARGET_MIPS
        int argv = env->active_tc.gpr[5];
#elif defined(TARGET_ARM)
        int argv = env->regs[1];
#endif
        int cmd_addr = 0;
        DECAF_read_ptr(cpu, argv + 4, &cmd_addr);
        DECAF_read_ptr(cpu, argv + 8, &feed_addr);
        char cmd_str[256];
        DECAF_read_mem(cpu, cmd_addr, 256, cmd_str);
        DECAF_printf("cmd is %s\n", cmd_str);
        char content[1024];
        DECAF_read_mem(cpu, feed_addr, 1024, content);
        DECAF_printf("content is %s\n", content);
        get_page_addr_code(env, feed_addr); //important
        get_page_addr_code(env, feed_addr+0x1000); //important
        DECAF_printf("pre get addr:%x,%x\n", feed_addr, feed_addr+0x1000);


    }
    else if(strcmp(feed_type, "NONE") == 0)
    {

    }
    else
    {
        DECAF_printf("feed type error\n");
        sleep(100);
    }
    
}

//a-z：97-122
//A-Z：65-90
//0-9：48-57
int check_input(char * input, int len) // if all are readable charater before =
{   
    int i = 0;
    while((input[i]>=97 && input[i]<=122) || (input[i]>=65 && input[i]<=90) || (input[i]>=48 && input[i]<=57))
    {
        i++;
        if(i == len)
        {
            return 1;
        }
        if(input[i] == '=')
        {
            return 1;
        }
    }
    return 0;
}

int check_http_header(char * input) // if all are readable charater before =
{   
    if(program_id == 9925)
    {
        if(strncmp(input, "GET /session_login.php HTTP/1.1", 31) == 0)
        {
            return 1;
        }
        else
        {
            return 0;
        }
    }
    else if(program_id == 10853)
    {
        if(strncmp(input, "POST /HNAP1/ HTTP/1.1", 21) == 0)
        {
            return 1;
        }
        else
        {
            return 0;
        }

    }
    else if(program_id == 161161)
    {
        if(strncmp(input, "POST /apply.cgi HTTP/1.1\r\n", 26) == 0)
        {
            return 1;
        }
        else
        {
            return 0;
        }

    }

    return 1;
}

int feed_input(CPUState * cpu)
{
    if(strcmp(feed_type, "FEED_ENV") == 0)
    {
        if(pre_feed_finish == 0)
            return 0;


        //char orig1_input_buf[MAX_LEN];
        //memset(orig_input_buf, 0, MAX_LEN);
        //DECAF_read_mem(cpu, content_addr, MAX_LEN, orig_input_buf);
        //DECAF_printf("orig_input:%s\n", orig_input_buf);
        


        char input_buf[MAX_LEN];
        int get_len = getWork(input_buf, MAX_LEN);
        if(check_input(input_buf, 1) == 0)
        {
            return 2;
        }
        //DECAF_printf("feed_input: %x, %s\n", content_addr, input_buf);
        int ret = DECAF_write_mem(cpu, content_addr, get_len, input_buf);
        DECAF_write_mem(cpu, content_addr + get_len, 1, "\0"); //important


        /*
        int tmp_content_addr = 0;
        int tmp_environ_addr = environ_addr;
        read_ptr(cpu, tmp_environ_addr, &tmp_content_addr);
        while(tmp_content_addr!=0)
        {
            char orig_input_buf[MAX_LEN];
            memset(orig_input_buf, 0, MAX_LEN);
            DECAF_read_mem(cpu, tmp_content_addr, MAX_LEN, orig_input_buf);
            DECAF_printf("tmp_content_addr:%x, orig_input:%s\n", tmp_content_addr, orig_input_buf);
            tmp_environ_addr+=4;
            read_ptr(cpu, tmp_environ_addr, &tmp_content_addr);
        } 
        */       

        return 1;
    }
    else if(strcmp(feed_type, "FEED_HTTP") == 0) 
    {
        //DECAF_printf("feed input -----------\n");
        /*
        if(pre_feed_finish == 0)
            return 0;
        CPUArchState *env = cpu->env_ptr;
        char input_buf[MAX_LEN-100];
        int get_len = getWork(input_buf, MAX_LEN-100);
        if(get_len > 2800)
        {
            get_len = 2700;
        }

        int tmp_addr = write_package(cpu, feed_addr, input_buf, get_len);
        DECAF_write_mem(cpu, tmp_addr, 1, "\0"); //important

#ifdef TARGET_MIPS
        env->active_tc.gpr[2] = tmp_addr - feed_addr;
        //DECAF_printf("modified length:%d\n", env->active_tc.gpr[2]);
        char tt[4096];
        DECAF_read_mem(cpu, feed_addr, 4096, tt);
        DECAF_printf("modified content:########%s\n", tt);
#else defined(TARGET_ARM)
        env->regs[0] = tmp_addr - feed_addr;
#endif
        return 1;
        */
        total_len = getWork(recv_buf, 4096);
        
        
        if(check_http_header(recv_buf) == 0)
        {
            //printf("recv_buf:%s\n", recv_buf);
            return 2;
        }
        
        //DECAF_printf("recv_buf:%s\n", recv_buf);
    }
    else if(strcmp(feed_type, "FEED_CMD") == 0)
    {
        /*
        CPUArchState *env = cpu->env_ptr;
        int argv = env->active_tc.gpr[5];
        int cmd_addr = 0;
        DECAF_read_ptr(cpu, argv + 4, &cmd_addr);
        DECAF_printf("cmd addr:%x\n", cmd_addr);
        char cmd_str[256];
        DECAF_read_mem(cpu, cmd_addr, 256, cmd_str);
        printf("cmd is %s\n", cmd_str);
        */
        char input_buf[MAX_LEN];
        int get_len = getWork(input_buf, MAX_LEN);
        //DECAF_printf("new inputs:%s, len:%d\n", input_buf, get_len);
        target_ulong tmp_addr = feed_addr;
        tmp_addr = write_package(cpu, feed_addr, input_buf, get_len);
        write_package(cpu, tmp_addr, "\0", 1); //important

    }
    else if(strcmp(feed_type, "NONE") == 0)
    {

    }
    else
    {
        DECAF_printf("feed type error\n");
        sleep(100);
    }
}
#endif

#ifdef AUTO_FIND_FORK_PC

/*
int check_arg(CPUState *cpu , char * arg_name)
{
    CPUArchState *env = cpu->env_ptr;
#ifdef TARGET_MIPS
    int argv = env->active_tc.gpr[5];
#elif defined(TARGET_ARM)
    int argv = env->regs[1];
#endif
    int sec_arg_addr;
    read_ptr(cpu, argv+4, &sec_arg_addr);
    char actual_name[100];
    DECAF_read_mem(cpu, sec_arg_addr, 100, actual_name);
    DECAF_printf("check:%x,%x,%s\n", argv, sec_arg_addr, actual_name);
    if(strcmp(arg_name, actual_name) == 0)
    {
        return 1;
    }
    return 0;
}
*/
#endif


#include "DECAF_types.h"
#include "DECAF_main.h"
#include "DECAF_callback.h"
#include "vmi_callback.h"
#include "utils/Output.h"
#include "vmi_c_wrapper.h"
int in_httpd = 0;
struct timeval store_page_start;
struct timeval store_page_end;
static DECAF_Handle processbegin_handle = DECAF_NULL_HANDLE;
static DECAF_Handle removeproc_handle = DECAF_NULL_HANDLE;
static DECAF_Handle block_begin_handle = DECAF_NULL_HANDLE;
static DECAF_Handle block_end_handle = DECAF_NULL_HANDLE;
static DECAF_Handle mem_write_cb_handle = DECAF_NULL_HANDLE;


int data_length(unsigned long value)
{
    int data_len = 0; //byte
    if((value & 0xffffff00) == 0)
    {
        data_len = 1;
    }
    else if((value & 0xffff0000) == 0)
    {
        data_len = 2;
    }
    else
    {
        data_len = 4;
    }
    return data_len;    
}

//extern FILE *file_log;
int mem_mapping_exit = 0;

static void do_block_begin(DECAF_Callback_Params* param)
{

    CPUState *cpu = param->bb.env;
    CPUArchState *env = cpu->env_ptr;
    target_ulong pc = param->bb.tb->pc;
#ifdef TARGET_MIPS
    target_ulong ra = env->active_tc.gpr[31];
#elif defined(TARGET_ARM)
    target_ulong ra = 0;
#endif

#ifdef FUZZ
    if(afl_user_fork && (pc == 0x80133a84 || pc == 0x80133ac4))
    {
        DECAF_printf("print_fatal_signal:%x\n",pc);
#ifdef FORK_OR_NOT
        int ret_value = 32;
        doneWork(ret_value);
        //goto end;
#endif
/*
#ifdef MEM_MAPPING
        target_ulong pgd = DECAF_getPGD(cpu);
        if(pgd == target_pgd)
        {
            mem_mapping_exit = 1;
        }
#endif
*/
    }
#endif

#ifdef STORE_PAGE_FUNC
#ifdef SNAPSHOT_SYNC
    if(afl_user_fork)
    {
        target_ulong pgd = DECAF_getPGD(cpu);
        if(pgd == target_pgd)
        {
            in_httpd = 1;
        }
        else
        {
            in_httpd = 0;
        }
    }
#endif
#endif
    return;
}

/*
static void do_block_end(DECAF_Callback_Params* param){ 
    return;

}
*/
#ifdef STORE_PAGE_FUNC
static void fuzz_mem_write(DECAF_Callback_Params *dcp)
{

    if(afl_user_fork == 1)
    {
        uint32_t next_page = 0;
        uint32_t virt_addr = dcp->mw.vaddr;
        uint32_t phys_addr = dcp->mw.paddr; 
        uintptr_t host_addr = dcp->mw.haddr; //64bit
        int dt = dcp->mw.dt;
        unsigned long value = dcp->mw.value;
        uintptr_t page_host_addr = host_addr & 0xfffffffffffff000;
        int dl = data_length(value);
        if(dl>0x1000)
        {
            printf("data too long, cross page\n");
            sleep(100);
            exit(32);
        }
        if ((virt_addr & 0xfff) + dl > 0x1000)
        { 
            DECAF_printf("cross page:%lx, len:%d\n\n\n\n\n", virt_addr, dl);
            next_page = (virt_addr & 0xfffff000) + 0x1000;
            sleep(100);
            exit(32);
            
        } 
// memory consistence
#ifdef SNAPSHOT_SYNC
        if(in_httpd && (virt_addr < kernel_base))
        {

            int ifexist = if_physical_exist(phys_addr & 0xfffff000);
            if(ifexist)
            {
                return;
            }
            add_physical_page(phys_addr & 0xfffff000);
        }
#endif

#ifdef CAL_TIME_ext
        gettimeofday(&store_page_start, NULL);
#endif
        store_page(virt_addr & 0xfffff000, page_host_addr, in_httpd);
#ifdef CAL_TIME_ext
        gettimeofday(&store_page_end, NULL);
        double store_once_time = (double)store_page_end.tv_sec - store_page_start.tv_sec + (store_page_end.tv_usec - store_page_start.tv_usec)/1000000.0;
        full_store_page_time += store_once_time;
#endif

    }

}
#endif

extern int afl_is_fuzzing;
typedef struct 
{
    target_ulong pgd;
    struct PGD * next;
}PGD;

PGD *pgd_head = NULL;

bool pgd_exist()
{
    if(pgd_head!=NULL)
    {
        return true;
    }
    return false;
}

void insert_pgd(int pgd)
{
    PGD * new_pgd = (PGD *)malloc(sizeof(PGD));
    new_pgd -> pgd = pgd;
    if(pgd_head == NULL)
    {
        pgd_head = new_pgd;
        new_pgd -> next = NULL;
    }
    else
    {
        PGD * tmp = pgd_head;
        pgd_head = new_pgd;
        new_pgd -> next = tmp;
    }
}


bool find_pgd(int pgd)
{
    for(PGD * curr =pgd_head; curr!=NULL; curr = curr->next)
    {
        int tmp_pgd = curr->pgd;
        if(tmp_pgd == pgd)
        {
            return true;
        }
    }
    return false;
}

bool delete_pgd(int pgd)
{
    PGD * last = NULL;
    for(PGD * curr = pgd_head; curr!=NULL; curr = curr->next)
    {
        if(curr->pgd == pgd)
        {
            if(last == NULL)
            {
                pgd_head = curr->next;
                free(curr); 
                curr = NULL;
            }
            else
            {
                last->next = curr->next;
                free(curr);
                curr = NULL;
            }
            return TRUE;

        }
        last = curr;
    }
    return FALSE;
}

static void callbacktests_loadmainmodule_callback(VMI_Callback_Params* params)
{
    char procname[64];
    uint32_t pid;
    uint32_t par_pid;
    char par_proc_name[100];
    int par_cr3;
    if (params == NULL)
    {
        return;
    }

    //VMI_find_process_by_cr3_c(params->cp.cr3, procname, 64, &pid);
    VMI_find_process_by_cr3_all(params->cp.cr3, procname, 64, &pid, &par_pid);
    //printf("new process:%s,%x\n", procname, params->cp.cr3);
    if (pid == (uint32_t)(-1))
    {
        return;
    }
    VMI_find_process_by_pid_c(par_pid, par_proc_name, 100, &par_cr3);

    if((strstr(par_proc_name,program_analysis)!=NULL) && (strstr(procname,program_analysis) ==NULL)){
        DECAF_printf("\n[+] Procname:%s/%d,pid:%d:%d, cur pgd:%x\n",procname, index, pid, par_pid, params->cp.cr3);
        DECAF_printf("parent proc:%s\n", par_proc_name);
        insert_pgd(params->cp.cr3);
        return;
    }
    if(strstr(procname,program_analysis) !=NULL)
    {
        DECAF_printf("\n[+] Procname:%s/%d,pid:%d:%d, cur pgd:%x\n",procname, index, pid, par_pid, params->cp.cr3);
        DECAF_printf("parent proc:%s\n", par_proc_name);
        insert_pgd(params->cp.cr3);
        return;

        //pro_start = 1;
        //flush_not_regen_pc();
       
    }
  
}
int exit_code=0xdeaddead;
static void callbacktests_removeproc_callback(VMI_Callback_Params* params)
{

    char procname[64];
    uint32_t pid;
    uint32_t par_pid;
    char par_proc_name[100];
     int par_cr3;

    if (params == NULL)
    {
        return;
    }
    VMI_find_process_by_cr3_all(params->cp.cr3, procname, 64, &pid, &par_pid);

    if (pid == (uint32_t)(-1))
    {
        return;
    }

    VMI_find_process_by_pid_c(par_pid, par_proc_name, 100, &par_cr3);

    if(strcmp(procname,program_analysis) == 0)
    {
        DECAF_printf("\n[-] Procname end:%s/%d,pid:%d, cur pgd:%x\n",procname, index, pid, params->rp.cr3);
        printf("process %s's exit_code is %d\n",procname,params->rp.exit_code);
        delete_pgd(params->rp.cr3);
        if(! pgd_exist()){
            exit_code=params->rp.exit_code;
        }
        return;
    }
    if((strstr(par_proc_name,program_analysis)!=NULL) && (strstr(procname,program_analysis) ==NULL)){
        DECAF_printf("\n[-] Procname:%s/%d,pid:%d:%d, cur pgd:%x\n",procname, index, pid, par_pid, params->cp.cr3);
        printf("process %s's exit_code is %d\n",procname,params->rp.exit_code);
        delete_pgd(params->rp.cr3);
        if(params->rp.exit_code!=0){
            exit_code=params->rp.exit_code;
        }
        return;
    }

}

int callbacktests_init(void)
{
    DECAF_output_init(NULL);
    DECAF_printf("Hello World\n");
    processbegin_handle = VMI_register_callback(VMI_CREATEPROC_CB, &callbacktests_loadmainmodule_callback, NULL);
    removeproc_handle = VMI_register_callback(VMI_REMOVEPROC_CB, &callbacktests_removeproc_callback, NULL);

    block_begin_handle = DECAF_registerOptimizedBlockBeginCallback(&do_block_begin, NULL, INV_ADDR, OCB_ALL);            
    return (0);
}


/* -icount align implementation. */

typedef struct SyncClocks {
    int64_t diff_clk;
    int64_t last_cpu_icount;
    int64_t realtime_clock;
} SyncClocks;

#if !defined(CONFIG_USER_ONLY)
/* Allow the guest to have a max 3ms advance.
 * The difference between the 2 clocks could therefore
 * oscillate around 0.
 */
#define VM_CLOCK_ADVANCE 3000000
#define THRESHOLD_REDUCE 1.5
#define MAX_DELAY_PRINT_RATE 2000000000LL
#define MAX_NB_PRINTS 100

static void align_clocks(SyncClocks *sc, const CPUState *cpu)
{
    int64_t cpu_icount;

    if (!icount_align_option) {
        return;
    }

    cpu_icount = cpu->icount_extra + cpu->icount_decr.u16.low;
    sc->diff_clk += cpu_icount_to_ns(sc->last_cpu_icount - cpu_icount);
    sc->last_cpu_icount = cpu_icount;

    if (sc->diff_clk > VM_CLOCK_ADVANCE) {
#ifndef _WIN32
        struct timespec sleep_delay, rem_delay;
        sleep_delay.tv_sec = sc->diff_clk / 1000000000LL;
        sleep_delay.tv_nsec = sc->diff_clk % 1000000000LL;
        if (nanosleep(&sleep_delay, &rem_delay) < 0) {
            sc->diff_clk = rem_delay.tv_sec * 1000000000LL + rem_delay.tv_nsec;
        } else {
            sc->diff_clk = 0;
        }
#else
        Sleep(sc->diff_clk / SCALE_MS);
        sc->diff_clk = 0;
#endif
    }
}

static void print_delay(const SyncClocks *sc)
{
    static float threshold_delay;
    static int64_t last_realtime_clock;
    static int nb_prints;

    if (icount_align_option &&
        sc->realtime_clock - last_realtime_clock >= MAX_DELAY_PRINT_RATE &&
        nb_prints < MAX_NB_PRINTS) {
        if ((-sc->diff_clk / (float)1000000000LL > threshold_delay) ||
            (-sc->diff_clk / (float)1000000000LL <
             (threshold_delay - THRESHOLD_REDUCE))) {
            threshold_delay = (-sc->diff_clk / 1000000000LL) + 1;
            printf("Warning: The guest is now late by %.1f to %.1f seconds\n",
                   threshold_delay - 1,
                   threshold_delay);
            nb_prints++;
            last_realtime_clock = sc->realtime_clock;
        }
    }
}

static void init_delay_params(SyncClocks *sc,
                              const CPUState *cpu)
{
    if (!icount_align_option) {
        return;
    }
    sc->realtime_clock = qemu_clock_get_ns(QEMU_CLOCK_VIRTUAL_RT);
    sc->diff_clk = qemu_clock_get_ns(QEMU_CLOCK_VIRTUAL) - sc->realtime_clock;
    sc->last_cpu_icount = cpu->icount_extra + cpu->icount_decr.u16.low;
    if (sc->diff_clk < max_delay) {
        max_delay = sc->diff_clk;
    }
    if (sc->diff_clk > max_advance) {
        max_advance = sc->diff_clk;
    }

    /* Print every 2s max if the guest is late. We limit the number
       of printed messages to NB_PRINT_MAX(currently 100) */
    print_delay(sc);
}
#else
static void align_clocks(SyncClocks *sc, const CPUState *cpu)
{
}

static void init_delay_params(SyncClocks *sc, const CPUState *cpu)
{
}
#endif /* CONFIG USER ONLY */

int last_log_pc = 0;
int prev_pc=0xdeaddead;
/* Execute a TB, and fix up the CPU state afterwards if necessary */
static inline tcg_target_ulong cpu_tb_exec(CPUState *cpu, TranslationBlock *itb)
{
    CPUArchState *env = cpu->env_ptr;
    uintptr_t ret;
    TranslationBlock *last_tb;
    int tb_exit;
    uint8_t *tb_ptr = itb->tc_ptr;
    target_ulong pc;
    target_ulong pgd;

    qemu_log_mask_and_addr(CPU_LOG_EXEC, itb->pc,
                           "Trace %p [%d: " TARGET_FMT_lx "] %s\n",
                           itb->tc_ptr, cpu->cpu_index, itb->pc,
                           lookup_symbol(itb->pc));

#if defined(DEBUG_DISAS)
    if (qemu_loglevel_mask(CPU_LOG_TB_CPU)
        && qemu_log_in_addr_range(itb->pc)) {
        qemu_log_lock();
#if defined(TARGET_I386)
        log_cpu_state(cpu, CPU_DUMP_CCOP);
#else
        log_cpu_state(cpu, 0);
#endif
        qemu_log_unlock();
    }
#endif /* DEBUG_DISAS */

    cpu->can_do_io = !use_icount;

    target_ulong CP0_Config1=0;
        #ifdef TARGET_MIPS
            pc = env->active_tc.PC;
            CP0_Config1=env->CP0_Config1;
            // target_ulong stack = env->active_tc.gpr[29];
        #elif defined(TARGET_ARM)
            pc = env->regs[15];
            // target_ulong stack = env->regs[13]; //???????
        #endif
            if(unlikely(afl_is_start==0)){
                afl_setup();
                printf("[*] afl is now start!!!\n");
                afl_is_start=1;
            }
            int flag=0;
            int pipe_ret=read(FORKSRV_FD,&flag,4);
            if (pipe_ret == -1) {
                if (errno == EAGAIN || errno == EWOULDBLOCK) {
                        // 当前没有数据可读，可以稍后再尝试
                        // printf("No data available right now. Try again later.\n");
                } else {
                        // 其他错误，打印错误信息
                    perror("read");
                    return EXIT_FAILURE;
                }
            }else if(pipe_ret==4){
                if(flag==255){
                        //开始插桩
                    // printf("[*] qemu start fuzz\n");
                    afl_is_fuzzing=1;
                    prev_loc=0;
                    if (write(FORKSRV_FD + 1, &flag, 4) != 4) {
                        perror("write");
                        return EXIT_FAILURE;
                    }
                }else if(flag==256){
                        
                    // printf("[*] qemu end fuzz\n");
                    afl_is_fuzzing=0;
                    if (write(FORKSRV_FD + 1, &system_flag, 4) != 4) {
                        perror("write");
                        return EXIT_FAILURE;
                    }
                    system_flag=0xdeaddead;
                }else if(flag==257){
                    //结束插桩,返回值
                    // printf("[*] qemu analyze exit_code\n");
                    if (write(FORKSRV_FD + 1, &exit_code, 4) != 4) {
                        perror("write");
                        return EXIT_FAILURE;
                    }
                    exit_code=0xdeaddead;
                }
            }
            
            if(unlikely(pgd_exist())){
                
                pgd=DECAF_getPGD(cpu);
                    if(pgd){
                        if(find_pgd(pgd)){
                            if(pc <0x80000000){
                                if(prev_pc!=pc){
                                    prev_pc=pc;
                                    if(pc==0x0042D960){
                                        system_flag=0x01020304;
                                    }
                                    if(unlikely(afl_is_fuzzing==1)){
                                        printf("[*] pc:0x%lx\n",pc);
                                        afl_maybe_log(pc>>4);
                                    }
                                }
                            // printf("[*] get it pc:0x%lx\n",pc);
                            }
                        }
                    }
            }
    ret = tcg_qemu_tb_exec(env, tb_ptr);
    cpu->can_do_io = 1;
    last_tb = (TranslationBlock *)(ret & ~TB_EXIT_MASK);
    tb_exit = ret & TB_EXIT_MASK;

    trace_exec_tb_exit(last_tb, tb_exit);

    if (tb_exit > TB_EXIT_IDX1) {
        /* We didn't start executing this TB (eg because the instruction
         * counter hit zero); we must restore the guest PC to the address
         * of the start of the TB.
         */
        CPUClass *cc = CPU_GET_CLASS(cpu);
        qemu_log_mask_and_addr(CPU_LOG_EXEC, last_tb->pc,
                               "Stopped execution of TB chain before %p ["
                               TARGET_FMT_lx "] %s\n",
                               last_tb->tc_ptr, last_tb->pc,
                               lookup_symbol(last_tb->pc));
        if (cc->synchronize_from_tb) {
            cc->synchronize_from_tb(cpu, last_tb);
        } else {
            assert(cc->set_pc);
            cc->set_pc(cpu, last_tb->pc);
        }
    }
    else
    {
        
    }
    return ret;
}

#ifndef CONFIG_USER_ONLY
/* Execute the code without caching the generated code. An interpreter
   could be used if available. */
static void cpu_exec_nocache(CPUState *cpu, int max_cycles,
                             TranslationBlock *orig_tb, bool ignore_icount)
{
    TranslationBlock *tb;

    /* Should never happen.
       We only end up here when an existing TB is too long.  */
    if (max_cycles > CF_COUNT_MASK)
        max_cycles = CF_COUNT_MASK;

    tb_lock();
    tb = tb_gen_code(cpu, orig_tb->pc, orig_tb->cs_base, orig_tb->flags,
                     max_cycles | CF_NOCACHE
                         | (ignore_icount ? CF_IGNORE_ICOUNT : 0));
    tb->orig_tb = orig_tb;
    tb_unlock();

    /* execute the generated code */
    trace_exec_tb_nocache(tb, tb->pc);
    cpu_tb_exec(cpu, tb);

    tb_lock();
    tb_phys_invalidate(tb, -1);
    tb_free(tb);
    tb_unlock();
}
#endif

static void cpu_exec_step(CPUState *cpu)
{
    CPUClass *cc = CPU_GET_CLASS(cpu);
    CPUArchState *env = (CPUArchState *)cpu->env_ptr;
    TranslationBlock *tb;
    target_ulong cs_base, pc;
    uint32_t flags;

    cpu_get_tb_cpu_state(env, &pc, &cs_base, &flags);
    if (sigsetjmp(cpu->jmp_env, 0) == 0) {
        mmap_lock();
        tb_lock();
        tb = tb_gen_code(cpu, pc, cs_base, flags,
                         1 | CF_NOCACHE | CF_IGNORE_ICOUNT);
        tb->orig_tb = NULL;
        tb_unlock();
        mmap_unlock();

        cc->cpu_exec_enter(cpu);
        /* execute the generated code */
        trace_exec_tb_nocache(tb, pc);
        cpu_tb_exec(cpu, tb);
        cc->cpu_exec_exit(cpu);

        tb_lock();
        tb_phys_invalidate(tb, -1);
        tb_free(tb);
        tb_unlock();
    } else {
        /* We may have exited due to another problem here, so we need
         * to reset any tb_locks we may have taken but didn't release.
         * The mmap_lock is dropped by tb_gen_code if it runs out of
         * memory.
         */
#ifndef CONFIG_SOFTMMU
        tcg_debug_assert(!have_mmap_lock());
#endif
        tb_lock_reset();
    }
}

void cpu_exec_step_atomic(CPUState *cpu)
{
    start_exclusive();

    /* Since we got here, we know that parallel_cpus must be true.  */
    parallel_cpus = false;
    cpu_exec_step(cpu);
    parallel_cpus = true;

    end_exclusive();
}

struct tb_desc {
    target_ulong pc;
    target_ulong cs_base;
    CPUArchState *env;
    tb_page_addr_t phys_page1;
    uint32_t flags;
    uint32_t trace_vcpu_dstate;
};

static bool tb_cmp(const void *p, const void *d)
{
    const TranslationBlock *tb = p;
    const struct tb_desc *desc = d;

    if (tb->pc == desc->pc &&
        tb->page_addr[0] == desc->phys_page1 &&
        tb->cs_base == desc->cs_base &&
        tb->flags == desc->flags &&
        tb->trace_vcpu_dstate == desc->trace_vcpu_dstate &&
        !atomic_read(&tb->invalid)) {
        /* check next page if needed */
        if (tb->page_addr[1] == -1) {
            return true;
        } else {
            tb_page_addr_t phys_page2;
            target_ulong virt_page2;

            virt_page2 = (desc->pc & TARGET_PAGE_MASK) + TARGET_PAGE_SIZE;
            phys_page2 = get_page_addr_code(desc->env, virt_page2);
            if (tb->page_addr[1] == phys_page2) {
                return true;
            }
        }
    }
    return false;
}

TranslationBlock *tb_htable_lookup(CPUState *cpu, target_ulong pc,
                                   target_ulong cs_base, uint32_t flags)
{
    tb_page_addr_t phys_pc;
    struct tb_desc desc;
    uint32_t h;

    desc.env = (CPUArchState *)cpu->env_ptr;
    desc.cs_base = cs_base;
    desc.flags = flags;
    desc.trace_vcpu_dstate = *cpu->trace_dstate;
    desc.pc = pc;
    phys_pc = get_page_addr_code(desc.env, pc);
    desc.phys_page1 = phys_pc & TARGET_PAGE_MASK;
    h = tb_hash_func(phys_pc, pc, flags, *cpu->trace_dstate);
    return qht_lookup(&tcg_ctx.tb_ctx.htable, tb_cmp, &desc, h);
}

static inline TranslationBlock *tb_find(CPUState *cpu,
                                        TranslationBlock *last_tb,
                                        int tb_exit)
{
    CPUArchState *env = (CPUArchState *)cpu->env_ptr;
    TranslationBlock *tb;
    target_ulong cs_base, pc;
    uint32_t flags;
    bool have_tb_lock = false;

    /* we record a subset of the CPU state. It will
       always be the same before a given translated block
       is executed. */
    cpu_get_tb_cpu_state(env, &pc, &cs_base, &flags);
    tb = atomic_rcu_read(&cpu->tb_jmp_cache[tb_jmp_cache_hash_func(pc)]);
    if (unlikely(!tb || tb->pc != pc || tb->cs_base != cs_base ||
                 tb->flags != flags ||
                 tb->trace_vcpu_dstate != *cpu->trace_dstate)) {
        tb = tb_htable_lookup(cpu, pc, cs_base, flags);
        if (!tb) {

            /* mmap_lock is needed by tb_gen_code, and mmap_lock must be
             * taken outside tb_lock. As system emulation is currently
             * single threaded the locks are NOPs.
             */
            mmap_lock();
            tb_lock();
            have_tb_lock = true;

            /* There's a chance that our desired tb has been translated while
             * taking the locks so we check again inside the lock.
             */
            tb = tb_htable_lookup(cpu, pc, cs_base, flags);
            if (!tb ) {
#ifdef CAL_TIME_ext
                if(afl_user_fork && into_syscall)
                {
                    gettimeofday(&syscall_codegen_begin, NULL);
                }
                else if(afl_user_fork)
                {
                    gettimeofday(&user_codegen_begin, NULL);
                }
#endif

                /* if no translated code available, then translate it now */
                tb = tb_gen_code(cpu, pc, cs_base, flags, 0);

#ifdef CAL_TIME_ext
                if(afl_user_fork && into_syscall) 
                {
                    gettimeofday(&syscall_codegen_end, NULL);
                    double block_codegen_time = (double)syscall_codegen_end.tv_sec - syscall_codegen_begin.tv_sec + (syscall_codegen_end.tv_usec - syscall_codegen_begin.tv_usec)/1000000.0;
                    syscall_codegen_time += block_codegen_time;
                }
                else if(afl_user_fork)
                {
                    gettimeofday(&user_codegen_end, NULL);
                    double block_codegen_time = (double)user_codegen_end.tv_sec - user_codegen_begin.tv_sec + (user_codegen_end.tv_usec - user_codegen_begin.tv_usec)/1000000.0;
                    user_codegen_time += block_codegen_time;
                }
#endif

            }

            mmap_unlock();
        }

        /* We add the TB in the virtual pc hash table for the fast lookup */
        atomic_set(&cpu->tb_jmp_cache[tb_jmp_cache_hash_func(pc)], tb);
    }


#ifndef CONFIG_USER_ONLY
    /* We don't take care of direct jumps when address mapping changes in
     * system emulation. So it's not safe to make a direct jump to a TB
     * spanning two pages because the mapping for the second page can change.
     */
    if (tb->page_addr[1] != -1) {
        last_tb = NULL;
    }
#endif
    /* See if we can patch the calling TB. */
   
    if (last_tb && !qemu_loglevel_mask(CPU_LOG_TB_NOCHAIN)) {
#ifndef FUZZ
        if (!have_tb_lock) {
            tb_lock();
            have_tb_lock = true;
        }

        if (!tb->invalid) {
            //跳过待fuzz程序的块链接
            if (last_tb->jmp_list_next[tb_exit]) {
                /* Another thread has already done this while we were
                * outside of the lock; nothing to do in this case */
               if (have_tb_lock) {
                    tb_unlock();
               }
                return tb;
            }
            // if(unlikely(pgd_exist())){
            //     target_ulong pgd=DECAF_getPGD(cpu);
            //     if(pgd){
            //         if(find_pgd(pgd)){
            //             // printf("[*] skip fuzz proc tb jmp\n");
            //             if (have_tb_lock) {
            //                 tb_unlock();
            //             }
            //             return tb;
            //         }
            //     }
            // }
            tb_add_jump(last_tb, tb_exit, tb);
        }
#endif
    }


    if (have_tb_lock) {
        tb_unlock();
    }
    return tb;
}

static inline bool cpu_handle_halt(CPUState *cpu)
{
    if (cpu->halted) {
#if defined(TARGET_I386) && !defined(CONFIG_USER_ONLY)
        if ((cpu->interrupt_request & CPU_INTERRUPT_POLL)
            && replay_interrupt()) {
            X86CPU *x86_cpu = X86_CPU(cpu);
            qemu_mutex_lock_iothread();
            apic_poll_irq(x86_cpu->apic_state);
            cpu_reset_interrupt(cpu, CPU_INTERRUPT_POLL);
            qemu_mutex_unlock_iothread();
        }
#endif
        if (!cpu_has_work(cpu)) {
            return true;
        }

        cpu->halted = 0;
    }

    return false;
}

static inline void cpu_handle_debug_exception(CPUState *cpu)
{
    CPUClass *cc = CPU_GET_CLASS(cpu);
    CPUWatchpoint *wp;

    if (!cpu->watchpoint_hit) {
        QTAILQ_FOREACH(wp, &cpu->watchpoints, entry) {
            wp->flags &= ~BP_WATCHPOINT_HIT;
        }
    }

    cc->debug_excp_handler(cpu);
}

static inline bool cpu_handle_exception(CPUState *cpu, int *ret)
{
    if (cpu->exception_index >= 0) {
        if (cpu->exception_index >= EXCP_INTERRUPT) {
            /* exit request from the cpu execution loop */
            *ret = cpu->exception_index;
            if (*ret == EXCP_DEBUG) {
                cpu_handle_debug_exception(cpu);
            }
            cpu->exception_index = -1;
            return true;
        } else {
#if defined(CONFIG_USER_ONLY)
            /* if user mode only, we simulate a fake exception
               which will be handled outside the cpu execution
               loop */
#if defined(TARGET_I386)
            CPUClass *cc = CPU_GET_CLASS(cpu);
            cc->do_interrupt(cpu);
#endif
            *ret = cpu->exception_index;
            cpu->exception_index = -1;
            return true;
#else
            if (replay_exception()) {
                CPUClass *cc = CPU_GET_CLASS(cpu);
                qemu_mutex_lock_iothread();
                cc->do_interrupt(cpu);
                qemu_mutex_unlock_iothread();
                cpu->exception_index = -1;
            } else if (!replay_has_interrupt()) {
                /* give a chance to iothread in replay mode */
                *ret = EXCP_INTERRUPT;
                return true;
            }
#endif
        }
#ifndef CONFIG_USER_ONLY
    } else if (replay_has_exception()
               && cpu->icount_decr.u16.low + cpu->icount_extra == 0) {
        /* try to cause an exception pending in the log */
        cpu_exec_nocache(cpu, 1, tb_find(cpu, NULL, 0), true);
        *ret = -1;
        return true;
#endif
    }

    return false;
}

static inline bool cpu_handle_interrupt(CPUState *cpu,
                                        TranslationBlock **last_tb)
{
    CPUClass *cc = CPU_GET_CLASS(cpu);

    if (unlikely(atomic_read(&cpu->interrupt_request))) {
        int interrupt_request;
        qemu_mutex_lock_iothread();
        interrupt_request = cpu->interrupt_request;
        if (unlikely(cpu->singlestep_enabled & SSTEP_NOIRQ)) {
            /* Mask out external interrupts for this step. */
            interrupt_request &= ~CPU_INTERRUPT_SSTEP_MASK;
        }
        if (interrupt_request & CPU_INTERRUPT_DEBUG) {
            cpu->interrupt_request &= ~CPU_INTERRUPT_DEBUG;
            cpu->exception_index = EXCP_DEBUG;
            qemu_mutex_unlock_iothread();
            return true;
        }
        if (replay_mode == REPLAY_MODE_PLAY && !replay_has_interrupt()) {
            /* Do nothing */
        } else if (interrupt_request & CPU_INTERRUPT_HALT) {
            replay_interrupt();
            cpu->interrupt_request &= ~CPU_INTERRUPT_HALT;
            cpu->halted = 1;
            cpu->exception_index = EXCP_HLT;
            qemu_mutex_unlock_iothread();
            return true;
        }
#if defined(TARGET_I386)
        else if (interrupt_request & CPU_INTERRUPT_INIT) {
            X86CPU *x86_cpu = X86_CPU(cpu);
            CPUArchState *env = &x86_cpu->env;
            replay_interrupt();
            cpu_svm_check_intercept_param(env, SVM_EXIT_INIT, 0, 0);
            do_cpu_init(x86_cpu);
            cpu->exception_index = EXCP_HALTED;
            qemu_mutex_unlock_iothread();
            return true;
        }
#else
        else if (interrupt_request & CPU_INTERRUPT_RESET) {
            replay_interrupt();
            cpu_reset(cpu);
            qemu_mutex_unlock_iothread();
            return true;
        }
#endif
        /* The target hook has 3 exit conditions:
           False when the interrupt isn't processed,
           True when it is, and we should restart on a new TB,
           and via longjmp via cpu_loop_exit.  */
        else {
            if (cc->cpu_exec_interrupt(cpu, interrupt_request)) {
                replay_interrupt();
                *last_tb = NULL;
            }
            /* The target hook may have updated the 'cpu->interrupt_request';
             * reload the 'interrupt_request' value */
            interrupt_request = cpu->interrupt_request;
        }
        if (interrupt_request & CPU_INTERRUPT_EXITTB) {
            cpu->interrupt_request &= ~CPU_INTERRUPT_EXITTB;
            /* ensure that no TB jump will be modified as
               the program flow was changed */
            *last_tb = NULL;
        }

        /* If we exit via cpu_loop_exit/longjmp it is reset in cpu_exec */
        qemu_mutex_unlock_iothread();
    }

    /* Finally, check if we need to exit to the main loop.  */
    if (unlikely(atomic_read(&cpu->exit_request)
        || (use_icount && cpu->icount_decr.u16.low + cpu->icount_extra == 0))) {
        atomic_set(&cpu->exit_request, 0);
        cpu->exception_index = EXCP_INTERRUPT;
        return true;
    }

    return false;
}

static inline void cpu_loop_exec_tb(CPUState *cpu, TranslationBlock *tb,
                                    TranslationBlock **last_tb, int *tb_exit)
{
    uintptr_t ret;
    int32_t insns_left;

    trace_exec_tb(tb, tb->pc);
    ret = cpu_tb_exec(cpu, tb);
    tb = (TranslationBlock *)(ret & ~TB_EXIT_MASK);
    *tb_exit = ret & TB_EXIT_MASK;
    if (*tb_exit != TB_EXIT_REQUESTED) {
        *last_tb = tb;
        return;
    }

    *last_tb = NULL;
    insns_left = atomic_read(&cpu->icount_decr.u32);
    atomic_set(&cpu->icount_decr.u16.high, 0);
    if (insns_left < 0) {
        /* Something asked us to stop executing chained TBs; just
         * continue round the main loop. Whatever requested the exit
         * will also have set something else (eg exit_request or
         * interrupt_request) which we will handle next time around
         * the loop.  But we need to ensure the zeroing of icount_decr
         * comes before the next read of cpu->exit_request
         * or cpu->interrupt_request.
         */
        smp_mb();
        return;
    }

    /* Instruction counter expired.  */
    assert(use_icount);
#ifndef CONFIG_USER_ONLY
    /* Ensure global icount has gone forward */
    cpu_update_icount(cpu);
    /* Refill decrementer and continue execution.  */
    insns_left = MIN(0xffff, cpu->icount_budget);
    cpu->icount_decr.u16.low = insns_left;
    cpu->icount_extra = cpu->icount_budget - insns_left;
    if (!cpu->icount_extra) {
        /* Execute any remaining instructions, then let the main loop
         * handle the next event.
         */
        if (insns_left > 0) {
            cpu_exec_nocache(cpu, insns_left, tb, false);
        }
    }
#endif
}
target_ulong ori_a1;
target_ulong ori_a3;
//#define SHOW_SYSCALL

/* main execution loop */
int cpu_exec(CPUState *cpu)
{
    CPUClass *cc = CPU_GET_CLASS(cpu);
    int ret;
    SyncClocks sc = { 0 };

    /* replay_interrupt may need current_cpu */
    current_cpu = cpu;

    if (cpu_handle_halt(cpu)) {
        return EXCP_HALTED;
    }

    rcu_read_lock();

    cc->cpu_exec_enter(cpu);

    /* Calculate difference between guest clock and host clock.
     * This delay includes the delay of the last cycle, so
     * what we have to do is sleep until it is 0. As for the
     * advance/delay we gain here, we try to fix it next time.
     */
    init_delay_params(&sc, cpu);

    /* prepare setjmp context for exception handling */
    if (sigsetjmp(cpu->jmp_env, 0) != 0) {
#if defined(__clang__) || !QEMU_GNUC_PREREQ(4, 6)
        /* Some compilers wrongly smash all local variables after
         * siglongjmp. There were bug reports for gcc 4.5.0 and clang.
         * Reload essential local variables here for those compilers.
         * Newer versions of gcc would complain about this code (-Wclobbered). */
        cpu = current_cpu;
        cc = CPU_GET_CLASS(cpu);
#else /* buggy compiler */
        /* Assert that the compiler does not smash local variables. */
        g_assert(cpu == current_cpu);
        g_assert(cc == CPU_GET_CLASS(cpu));
#endif /* buggy compiler */
        cpu->can_do_io = 1;
        tb_lock_reset();
        if (qemu_mutex_iothread_locked()) {
            qemu_mutex_unlock_iothread();
        }
    }
    CPUArchState * env = cpu->env_ptr;

    /* if an exception is pending, we execute it here */
    while (!cpu_handle_exception(cpu, &ret)) {
        TranslationBlock *last_tb = NULL;
        int tb_exit = 0;

        while (!cpu_handle_interrupt(cpu, &last_tb)) {
// #ifdef TARGET_MIPS
//             target_ulong pc = env->active_tc.PC;
//             // target_ulong stack = env->active_tc.gpr[29];
// #elif defined(TARGET_ARM)
//             target_ulong pc = env->regs[15];
//             // target_ulong stack = env->regs[13]; //???????
// #endif
//             if(unlikely(afl_is_start==0)){
//                 afl_setup();
//                 printf("[*] afl is now start!!!\n");
//                 afl_is_start=1;
//             }
//             int flag=0;
//             int ret=read(FORKSRV_FD,&flag,4);
//             if (ret == -1) {
//                 if (errno == EAGAIN || errno == EWOULDBLOCK) {
//                         // 当前没有数据可读，可以稍后再尝试
//                         // printf("No data available right now. Try again later.\n");
//                 } else {
//                         // 其他错误，打印错误信息
//                     perror("read");
//                     return EXIT_FAILURE;
//                 }
//             }else if(ret==4){
//                 if(flag==255){
//                         //开始插桩
//                     // printf("[*] qemu start fuzz\n");
//                     afl_is_fuzzing=1;
//                     prev_loc=0;
//                     if (write(FORKSRV_FD + 1, &flag, 4) != 4) {
//                         perror("write");
//                         return EXIT_FAILURE;
//                     }
//                 }else if(flag==256){
                        
//                     // printf("[*] qemu end fuzz\n");
//                     afl_is_fuzzing=0;
//                     if (write(FORKSRV_FD + 1, &system_flag, 4) != 4) {
//                         perror("write");
//                         return EXIT_FAILURE;
//                     }
//                     system_flag=0xdeaddead;
//                 }else if(flag==257){
//                     //结束插桩,返回值
//                     // printf("[*] qemu analyze exit_code\n");
//                     if (write(FORKSRV_FD + 1, &exit_code, 4) != 4) {
//                         perror("write");
//                         return EXIT_FAILURE;
//                     }
//                     exit_code=0xdeaddead;
//                 }
//             }
            
//             if(unlikely(pgd_exist())){
                
//                 target_ulong pgd=DECAF_getPGD(cpu);
//                     if(pgd){
//                         if(find_pgd(pgd)){
//                             if(pc<0x70000000){
//                                 printf("[*] pc:0x%lx",pc);
//                                 if(pc==0x0042D960||pc==0x0042D430){
//                                     system_flag=0x01020304;
//                                 }
//                                 // printf("[*] pc:0x%lx   cr3:%lx\n",pc,pgd);
//                                 if(unlikely(afl_is_fuzzing==1)){
//                                     afl_maybe_log(pc);
//                                 }
//                             // printf("[*] get it pc:0x%lx\n",pc);
//                             }
//                         }
//                     }
                
//             }
            TranslationBlock *tb = tb_find(cpu, last_tb, tb_exit);
            cpu_loop_exec_tb(cpu, tb, &last_tb, &tb_exit);
            /* Try to align the host and virtual clocks
               if the guest is in advance */
               align_clocks(&sc, cpu);
        }
    }

    cc->cpu_exec_exit(cpu);
    rcu_read_unlock();
    return ret;
}