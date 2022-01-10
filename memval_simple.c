/* ******************************************************************************
* Copyright (c) 2017-2021 Google, Inc.  All rights reserved.
* ******************************************************************************/

/*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*
* * Redistributions of source code must retain the above copyright notice,
*   this list of conditions and the following disclaimer.
*
* * Redistributions in binary form must reproduce the above copyright notice,
*   this list of conditions and the following disclaimer in the documentation
*   and/or other materials provided with the distribution.
*
* * Neither the name of VMware, Inc. nor the names of its contributors may be
*   used to endorse or promote products derived from this software without
*   specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
* AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
* IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
* ARE DISCLAIMED. IN NO EVENT SHALL VMWARE, INC. OR CONTRIBUTORS BE LIABLE
* FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
* DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
* SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
* CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
* LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
* OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
* DAMAGE.
*/

/* Code Manipulation API Sample:
* memval_simple.c
*
* Records and dumps app write addresses, and their corresponding written values.
*
* (1) It fills two per-thread-buffers with inlined instrumentation.
* (2) Once the buffers have been filled up, a fault handler will redirect execution
*     to our trace buffer handler, where we dump the memrefs to disk.
*
* This sample illustrates
* - inserting instrumentation after the current instruction to read the value
*   written by it;
* - the use of drutil_expand_rep_string() to expand string loops to obtain
*   every memory reference;
* - the use of drx_expand_scatter_gather() to expand scatter/gather instrs
*   into a set of functionally equivalent stores/loads;
* - the use of drutil_opnd_mem_size_in_bytes() to obtain the size of OP_enter
*   memory references;
* - the use of drutil_insert_get_mem_addr() to insert instructions to compute
*   the address of each memory reference;
* - the use of the drx_buf extension to fill buffers in a platform-independent
*   manner.
*
* This client is a simple implementation of a memory reference tracing tool
* without instrumentation optimization.
*/
//#include <criu/criu.h>
#include "dr_api.h"
#include "drmgr.h"
#include "drutil.h"
#include "drreg.h"
#include "utils.h"
#include "drx.h"
#include "drsyms.h"
#include "drwrap.h"

#include <libpmemobj/base.h>
#include <libpmemobj/pool_base.h>
#include <libpmemobj/types.h>
#include <libpmemobj/tx_base.h>
#include <stddef.h> /* for offsetof */
#include <string.h>
#include <unistd.h>
#include <signal.h>

//#include <fcntl.h>

#ifdef WINDOWS
#    define IF_WINDOWS_ELSE(x, y) x
#else
#    define IF_WINDOWS_ELSE(x, y) y
#endif

#ifdef WINDOWS
#    define DISPLAY_STRING(msg) dr_messagebox(msg)
#else
#    define DISPLAY_STRING(msg) dr_printf("%s\n", msg);
#endif

#define PMEM_AREA_SIZE 32000000

#define NULL_TERMINATE(buf) (buf)[(sizeof((buf)) / sizeof((buf)[0])) - 1] = '\0'

static PMEMobjpool *pop;
static PMEMoid root;
static struct my_root *rootp;

void initialize(size_t requested_pool_size);

static void
wrap_pre(void *wrapcxt, OUT void **user_data);
static void
wrap_post(void *wrapcxt, void *user_data);

static void
wrap_pre2(void *wrapcxt, OUT void **user_data);
static void
wrap_post2(void *wrapcxt, void *user_data);

static void
wrap_pre_tx_start(void *wrapcxt, OUT void **user_data);
static void
wrap_pre_tx_finish(void *wrapcxt, OUT void **user_data);

/* --- */
//static void initislise(void);
void create_unique_file_name(char *path_to_pmem);
//static void *create_and_map_persistent_memory_pool(void);

/* --- */

//#define MALLOC_ROUTINE_NAME IF_WINDOWS_ELSE("HeapAlloc", "malloc")
#define MALLOC_ROUTINE_NAME IF_WINDOWS_ELSE("mmap", "mmap")

bool file_exists(const char *path){
   return access(path, F_OK) != 0;
}
struct my_root {
    long oofset;
    char pmem_start[64000000];
};
/*
struct my_root {
   char this_is_on_pmem[PMEM_AREA_SIZE];
};
 */
/**
static const char *desc[] = {
   "TX_STAGE_NONE",
   "TX_STAGE_WORK",
   "TX_STAGE_ONCOMMIT",
   "TX_STAGE_ONABORT",
   "TX_STAGE_FINALLY",
   "WTF?"
};
**/

static void
log_stages(PMEMobjpool *pop_local, enum pobj_tx_stage stage, void *arg)
{
    /* Commenting this out because this is not required during normal execution. */
    /* dr_fprintf(STDERR, "cb stage: ", desc[stage], " "); */
}

static bool file_was_created = false;

static void
module_load_event(void *drcontext, const module_data_t *mod, bool loaded)
{
    const char *func_name = "sm_op_begin";
    app_pc orig;
    size_t offs;

    if (drsym_lookup_symbol(mod->full_path, func_name, &offs, DRSYM_DEMANGLE) == DRSYM_SUCCESS) {
        orig = offs + mod->start;
        dr_printf("function \"%s\" is found..\n", func_name);
        bool wrapped = drwrap_wrap(orig, wrap_pre_tx_start, NULL);
        if (wrapped) { dr_printf("function \"%s\" is wrapped..\n", func_name); }
    }

    func_name = "sm_op_end";


    if (drsym_lookup_symbol(mod->full_path, func_name, &offs, DRSYM_DEMANGLE) == DRSYM_SUCCESS) {
        orig = offs + mod->start;
        dr_printf("function \"%s\" is found..\n", func_name);
        bool wrapped = drwrap_wrap(orig, wrap_pre_tx_finish, NULL);
        if (wrapped) { dr_printf("function \"%s\" is wrapped..\n", func_name); }
    }
    /* This methos is called multiple times, but we only need to open the file once */
    if(!file_was_created) {
        file_was_created = true;
        initialize(128000000);
    }
    /**
    if(!file_was_created) {
        file_was_created = true;
        const char *path_to_pmem = "/mnt/dax/test_outputs/mmaped_files/wrap_pmem_file_0";

        if (file_exists((path_to_pmem)) != 0) {
            if ((pop = pmemobj_create(path_to_pmem, POBJ_LAYOUT_NAME(list),
                                      PMEMOBJ_MIN_POOL, 0666)) == NULL) {
                perror("failed to create pool\n");
            }
        } else {
            if ((pop = pmemobj_open(path_to_pmem, POBJ_LAYOUT_NAME(list))) == NULL) {
                perror("failed to open pool\n");
            }
        }
        root = pmemobj_root(pop, sizeof(struct my_root));
        rootp = pmemobj_direct(root);
    }
   **/
   app_pc towrap = (app_pc)dr_get_proc_address(mod->handle, MALLOC_ROUTINE_NAME);
   app_pc towrap2 = (app_pc)dr_get_proc_address(mod->handle, "munmap");
   if (towrap != NULL) {
#ifdef SHOW_RESULTS
       bool ok =
#endif
           drwrap_wrap(towrap, wrap_pre, wrap_post);
           drwrap_wrap(towrap2, wrap_pre2, wrap_post2);
#ifdef SHOW_RESULTS
       if (ok) {
           dr_fprintf(STDERR, "<wrapped " MALLOC_ROUTINE_NAME " @" PFX "\n", towrap);
           dr_fprintf(STDERR,   "%ld %ld \n", (long)getpid(), (long)getppid());
       } else {

           dr_fprintf(STDERR,
                      "<FAILED to wrap " MALLOC_ROUTINE_NAME " @" PFX
                      ": already wrapped?\n",
                      towrap);
       }
#endif
   }
}

static bool tx_active = false;
static void
wrap_pre_tx_start(void *wrapcxt, OUT void **user_data){
    perror("Starting a new transaction \n");
    pmemobj_tx_begin(pop, NULL, TX_PARAM_CB, log_stages, NULL,
                     TX_PARAM_NONE);

    tx_active = true;
}
static void
wrap_pre_tx_finish(void *wrapcxt, OUT void **user_data){
    perror("Commiting transaction! \n");
    pmemobj_tx_commit();
    pmemobj_tx_end();
    tx_active = false;
}

static void
wrap_pre(void *wrapcxt, OUT void **user_data)
{
    /* 0 for malloc, 1 for mmap */
   size_t sz = (size_t)drwrap_get_arg(wrapcxt, IF_WINDOWS_ELSE(2, 1));
   printf("MMAP size: %zu \n", sz);
   *user_data = (void *)sz;
}

static void
wrap_pre2(void *wrapcxt, OUT void **user_data)
{
    /* Need to match this with PMEMoid or file and release */
    //void *addr = (void *)(size_t)drwrap_get_arg(wrapcxt, 1);
    //munmap()
    perror("munmap called");
}

static void
wrap_post2(void *wrapcxt, void *user_data)
{
    drwrap_set_retval(wrapcxt, 0);

}

/**
 *
 */
static struct my_root *rootp;
void initialize(size_t requested_pool_size){

    /* Change to a safe imlementation */
    char *path_to_pmem = calloc(200, 1);
    create_unique_file_name(path_to_pmem);
    size_t pool_size = requested_pool_size;
    printf("Requested pool size: %zu MB\n", pool_size/1000000);
    if(pool_size < PMEMOBJ_MIN_POOL){
        pool_size = PMEMOBJ_MIN_POOL;
    }

    if (file_exists((path_to_pmem)) != 0) {
        if ((pop = pmemobj_create(path_to_pmem, POBJ_LAYOUT_NAME(list),
                                  pool_size, 0666)) == NULL) {
            perror("failed to create pool\n");
        }
    } else {
        if ((pop = pmemobj_open(path_to_pmem, POBJ_LAYOUT_NAME(list))) == NULL) {
            perror("failed to open pool\n");
        }
    }
    printf("Pool is provisioned!\n");
    //root = pmemobj_root(pop, sizeof(struct my_root));
    //rootp = pmemobj_direct(root);
    printf("Setting up initial values.\n");
    //rootp->oofset = 0;
    //long *t = &rootp->oofset;
    //t = 0;
    //uintptr_t *start = (uintptr_t *)rootp->pmem_start;
    //uintptr_t *current = (uintptr_t *)rootp->next_available_slot;
    //rootp->next_available_slot = rootp->pmem_start;
    //rootp->next_available_slot = start;
    printf("Setting is done!\n");
}

/* Needs to be inside a transaction, otherwise this space is wasted */
static long offset = 0;
void *allocate_space_on_pmem(size_t size){
    /* Case if pmem is free */
    printf("start\n");

    root = pmemobj_root(pop, sizeof(struct my_root));
    rootp = pmemobj_direct(root);

    //long *t = malloc(sizeof (long));
    //memcpy(t, &rootp->oofset, sizeof (long));
    //printf("Managed to read value! %lu\n", *t);
    void *currently_available_slot;
    if(offset == 0){
        printf("Pmem is empty\n");
        offset = size+10000;
        printf("ADDR: %p \n", rootp->pmem_start);
        return rootp->pmem_start;
    } else{
        /* Case if there is a reserved region on pmem */
        printf("Pmem is used\n");
        currently_available_slot = rootp->pmem_start + offset+10000;
        printf("ADDR: %p \n", currently_available_slot);
        offset = offset + size+10000;
        printf("end\n");
    }

    return currently_available_slot;
}

/** */
bool initialized = false;
static void
wrap_post(void *wrapcxt, void *user_data)
{

#ifdef SHOW_RESULTS
   size_t sz = (size_t)user_data;
   /** Condition to identify the target malloc
    * This needs to be generalized to pick memory allocations that we are looking for.
    **/
   //if(sz == PMEM_AREA_SIZE){
   //    perror("PMEM size request");

   //drwrap_set_retval(wrapcxt, rootp->this_is_on_pmem);
   //drwrap_set_retval(wrapcxt, create_and_map_persistent_memory_pool());
   printf("Allocating space \n");
   if(!initialized){
       //initialize(128000000);
       //initialized = true;
   }
   void *ptr = allocate_space_on_pmem(sz);
   printf("Space was allocated\n");
   drwrap_set_retval(wrapcxt, ptr);
   //}
#endif
}

/* We opt to use two buffers -- one to hold only mem_ref_t structs, and another to hold
* the raw bytes written. This is done for simplicity, as we will never get a partial
* write to the trace buffer (holding mem_ref_t's), which simplifies the handler logic.
*/
typedef struct _mem_ref_t {
   ushort size; /* mem ref size */
   ushort type; /* instr opcode */
   app_pc addr; /* mem ref addr */
} mem_ref_t;

/* Max number of mem_ref a buffer can have. */
#define MAX_NUM_MEM_REFS 4096
/* The maximum size of buffer for holding mem_refs. */
#define MEM_BUF_SIZE (sizeof(mem_ref_t) * MAX_NUM_MEM_REFS)
/* The maximum size of buffer for holding writes. Writes on average don't get too large,
* but we give ourselves some leeway and say chains of consecutive writes are on average
* less than 32 bytes each.
*/
#define WRT_BUF_SIZE (MAX_NUM_MEM_REFS * 32)

#define MINSERT instrlist_meta_preinsert

/* Thread-private log file. */
typedef struct {
   file_t log;
   FILE *logf;
} per_thread_t;

/* Cross-instrumentation-phase data. */
typedef struct {
   reg_id_t reg_addr;
   int last_opcode;
} instru_data_t;

static client_id_t client_id;
static int tls_idx;
static drx_buf_t *write_buffer;
static drx_buf_t *trace_buffer;

/* Requires that hex_buf be at least as long as 2*memref->size + 1. */
/*
static char *
write_hexdump(char *hex_buf, byte *write_base, mem_ref_t *mem_ref)
{
   int i;
   char *hexstring = hex_buf, *needle = hex_buf;

   for (i = mem_ref->size - 1; i >= 0; --i) {
       needle += dr_snprintf(needle, 2 * mem_ref->size + 1 - (needle - hex_buf), "%02x",
                             write_base[i]);
   }
   return hexstring;
}
*/
/* Called when the trace buffer has filled up, and needs to be flushed to disk. */
static void
trace_fault(void *drcontext, void *buf_base, size_t size)
{
  // per_thread_t *data = drmgr_get_tls_field(drcontext, tls_idx);
   mem_ref_t *trace_base = (mem_ref_t *)(char *)buf_base;
   mem_ref_t *trace_ptr = (mem_ref_t *)((char *)buf_base + size);
   //byte *write_base = drx_buf_get_buffer_base(drcontext, write_buffer);
   //byte *write_ptr = drx_buf_get_buffer_ptr(drcontext, write_buffer);
   int largest_size = 0;
   mem_ref_t *mem_ref;
   char *hex_buf;

   /* find the largest necessary buffer so we only perform a single allocation */
   for (mem_ref = trace_base; mem_ref < trace_ptr; mem_ref++) {
       if (mem_ref->size > largest_size)
           largest_size = mem_ref->size;
   }
   hex_buf = dr_thread_alloc(drcontext, 2 * largest_size + 1);
   /* write the memrefs to disk */
   for (mem_ref = trace_base; mem_ref < trace_ptr; mem_ref++) {
       /* Each memref in the trace buffer has an "associated" write in the write buffer.
        * We pull mem_ref->size bytes from the write buffer, and assert we haven't yet
        * gone too far.
        */
       /* We use libc's fprintf as it is buffered and much faster than dr_fprintf for
        * repeated printing that dominates performance, as the printing does here. Note
        * that a binary dump is *much* faster than fprintf still.
        */
        /*
       fprintf(data->logf, "" PFX ": %s %2d %s\n", mem_ref->addr,
               decode_opcode_name(mem_ref->type), mem_ref->size,
               write_hexdump(hex_buf, write_base, mem_ref)
       );
       write_base += mem_ref->size;
       DR_ASSERT(write_base <= write_ptr);
         */
   }
   dr_thread_free(drcontext, hex_buf, 2 * largest_size + 1);
   /* reset the write buffer (note: the trace buffer gets reset automatically) */
   drx_buf_set_buffer_ptr(drcontext, write_buffer,
                          drx_buf_get_buffer_base(drcontext, write_buffer));
}

static void catch_mem_ref(uintptr_t *addr, uintptr_t *pc, uint size);
static int op_count = 0;
static void catch_mem_ref(uintptr_t *addr, uintptr_t *pc, uint size){
   uintptr_t *start = (uintptr_t *)rootp->pmem_start;
   uintptr_t *finish = (uintptr_t *)rootp->pmem_start + PMEM_AREA_SIZE;

   /* Check if this operation is updating persistent memory */
   if(addr >= start && addr <=finish && tx_active == true){
       perror("Adding to transaction \n");
       pmemobj_tx_add_range_direct(addr, 64);
       /* Uncoment to text crash consistency */

       op_count++;
       if(op_count == 6){
           //raise(SIGSEGV);
           //pmemobj_tx_abort(1);
           //pmemobj_tx_get_failure_behavior();
       }



   }
}

static reg_id_t
instrument_pre_write(void *drcontext, instrlist_t *ilist, instr_t *where, int opcode,
                    instr_t *instr_operands, opnd_t ref)
{
   reg_id_t reg_ptr, reg_tmp, reg_addr;
   ushort type, size;
   bool ok;

   if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_tmp) !=
       DRREG_SUCCESS) {
       DR_ASSERT(false);
       return DR_REG_NULL;
   }
   if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
       DRREG_SUCCESS) {
       DR_ASSERT(false);
       return DR_REG_NULL;
   }

   /* i#2449: In the situation that instrument_post_write, instrument_pre_write and ref
    * all have the same register reserved, drutil_insert_get_mem_addr will compute the
    * address of an operand using an incorrect register value, as drreg will elide the
    * save/restore.
    */
   if (opnd_uses_reg(ref, reg_tmp) &&
       drreg_get_app_value(drcontext, ilist, where, reg_tmp, reg_tmp) != DRREG_SUCCESS) {
       DR_ASSERT(false);
       return DR_REG_NULL;
   }
   if (opnd_uses_reg(ref, reg_ptr) &&
       drreg_get_app_value(drcontext, ilist, where, reg_ptr, reg_ptr) != DRREG_SUCCESS) {
       DR_ASSERT(false);
       return DR_REG_NULL;
   }

   /* We use reg_ptr as scratch to get addr. Note we do this first as reg_ptr or reg_tmp
    * may be used in ref.
    */
   ok = drutil_insert_get_mem_addr(drcontext, ilist, where, ref, reg_tmp, reg_ptr);
   DR_ASSERT(ok);
   drx_buf_insert_load_buf_ptr(drcontext, trace_buffer, ilist, where, reg_ptr);
   /* inserts memref addr */

   drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, DR_REG_NULL,
                            opnd_create_reg(reg_tmp), OPSZ_PTR,
                            offsetof(mem_ref_t, addr));

   instr_t *instr = instrlist_first(ilist);
   app_pc pc_l = instr_get_app_pc(instr);

   opnd_t opnd = instr_get_src(instr,0);
   uint size_of_mem_ref = drutil_opnd_mem_size_in_bytes(opnd, instr);

   dr_insert_clean_call(drcontext,ilist,where,(void *)catch_mem_ref, false, 3,
                        opnd_create_reg(reg_tmp),
                        OPND_CREATE_INTPTR(pc_l),
                        OPND_CREATE_INT64(size_of_mem_ref)
   );
   if (IF_AARCHXX_ELSE(true, false)) {
       /* At this point we save the write address for later, because reg_tmp's value
        * will get clobbered on ARM.
        */
       if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_addr) !=
           DRREG_SUCCESS) {
           DR_ASSERT(false);
           return DR_REG_NULL;
       }
       MINSERT(ilist, where,
               XINST_CREATE_move(drcontext, opnd_create_reg(reg_addr),
                                 opnd_create_reg(reg_tmp)));
   }
   /* Inserts type. */
   type = (ushort)opcode;
   drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, reg_tmp,
                            OPND_CREATE_INT16(type), OPSZ_2, offsetof(mem_ref_t, type));
   /* Inserts size. */
   size = (ushort)drutil_opnd_mem_size_in_bytes(ref, instr_operands);
   drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr, reg_tmp,
                            OPND_CREATE_INT16(size), OPSZ_2, offsetof(mem_ref_t, size));
   /* If the app write segfaults, we will be unable to write to the write_buffer, which
    * means the above trace_buffer entries won't have a corresponding entry in the
    * write_buffer. To mitigate this scenario, we postpone updating trace_buffer ptr to
    * the post-write instrumentation. This way, if the app write fails for any reason,
    * the trace_buffer entry will not be committed.
    */

   if (instr_is_call(instr_operands)) {
       app_pc pc;

       /* Note that on ARM the call instruction writes only to the link register, so
        * we would never even get into instrument_pre_write() on ARM if this was a call.
        */
       IF_AARCHXX(DR_ASSERT(false));
       /* We simulate the call instruction's written memory by writing the next app_pc
        * to the written buffer, since we can't do this after the call has happened.
        */
       drx_buf_insert_load_buf_ptr(drcontext, write_buffer, ilist, where, reg_ptr);
       pc = decode_next_pc(drcontext, instr_get_app_pc(instr_operands));
       /* note that for a circular buffer, we don't need to specify a scratch register */
       drx_buf_insert_buf_store(drcontext, trace_buffer, ilist, where, reg_ptr,
                                DR_REG_NULL, OPND_CREATE_INTPTR((ptr_int_t)pc), OPSZ_PTR,
                                0);
       drx_buf_insert_update_buf_ptr(drcontext, write_buffer, ilist, where, reg_ptr,
                                     reg_tmp, sizeof(app_pc));
       /* we don't need to persist reg_tmp to the next instruction */
       if (drreg_unreserve_register(drcontext, ilist, where, reg_tmp) != DRREG_SUCCESS)
           DR_ASSERT(false);
       reg_tmp = DR_REG_NULL;
   } else if (IF_AARCHXX_ELSE(true, false)) {
       /* Now reg_tmp has the address of the write again. */
       MINSERT(ilist, where,
               XINST_CREATE_move(drcontext, opnd_create_reg(reg_tmp),
                                 opnd_create_reg(reg_addr)));
       if (drreg_unreserve_register(drcontext, ilist, where, reg_addr) != DRREG_SUCCESS)
           DR_ASSERT(false);
   }
   //char *ptr = malloc(1);
   //brk(ptr);
   if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS)
       DR_ASSERT(false);
   return reg_tmp;
}

static void
instrument_post_write(void *drcontext, instrlist_t *ilist, instr_t *where, opnd_t memref,
                     instr_t *write, reg_id_t reg_addr)
{
   reg_id_t reg_ptr;
   ushort stride = (ushort)drutil_opnd_mem_size_in_bytes(memref, write);

   /* We want to use the same predicate as write when inserting the following
    * instrumentation.
    */
   instrlist_set_auto_predicate(ilist, instr_get_predicate(write));

   if (drreg_reserve_register(drcontext, ilist, where, NULL, &reg_ptr) !=
       DRREG_SUCCESS) {
       DR_ASSERT(false);
       return;
   }

   drx_buf_insert_load_buf_ptr(drcontext, write_buffer, ilist, where, reg_ptr);
   /* drx_buf_insert_buf_memcpy() internally updates the buffer pointer */
   drx_buf_insert_buf_memcpy(drcontext, write_buffer, ilist, where, reg_ptr, reg_addr,
                             stride);

   /* Data was written to trace_buffer in instrument_pre_write. Here, by updating
    * the trace_buffer ptr, we essentially commit that data. See comment in
    * instrument_pre_write for more details.
    * XXX: This extra overhead of loading trace_buffer ptr in the common path can
    * be avoided by handling the app-write-fail case in a fault handler instead.
    */
   drx_buf_insert_load_buf_ptr(drcontext, trace_buffer, ilist, where, reg_ptr);
   drx_buf_insert_update_buf_ptr(drcontext, trace_buffer, ilist, where, reg_ptr,
                                 DR_REG_NULL, sizeof(mem_ref_t));

   if (drreg_unreserve_register(drcontext, ilist, where, reg_ptr) != DRREG_SUCCESS)
       DR_ASSERT(false);
   if (drreg_unreserve_register(drcontext, ilist, where, reg_addr) != DRREG_SUCCESS)
       DR_ASSERT(false);

   /* Set the predicate back to the default */
   instrlist_set_auto_predicate(ilist, instr_get_predicate(where));
}

static void
handle_post_write(void *drcontext, instrlist_t *ilist, instr_t *where, reg_id_t reg_addr)
{
   int i;
   instr_t *prev_instr = instr_get_prev_app(where);
   bool seen_memref = false;

   /* XXX: We assume that no write instruction has multiple distinct memory destinations.
    * This way we are able to persist a single register across an app instruction. Note
    * there are instructions which currently do break this assumption, but we punt on
    * this.
    */
   for (i = 0; i < instr_num_dsts(prev_instr); ++i) {
       if (opnd_is_memory_reference(instr_get_dst(prev_instr, i))) {
           if (seen_memref) {
               DR_ASSERT_MSG(false, "Found inst with multiple memory destinations");
               break;
           }
           seen_memref = true;
           instrument_post_write(drcontext, ilist, where, instr_get_dst(prev_instr, i),
                                 prev_instr, reg_addr);
       }
   }
}

static dr_emit_flags_t
event_app_analysis(void *drcontext, void *tag, instrlist_t *bb, bool for_trace,
                  bool translating, void **user_data)
{
   instru_data_t *data = (instru_data_t *)dr_thread_alloc(drcontext, sizeof(*data));
   data->reg_addr = DR_REG_NULL;
   data->last_opcode = OP_INVALID;
   *user_data = (void *)data;
   return DR_EMIT_DEFAULT;
}

/* For each memory reference app instr, we insert inline code to fill the buffer
* with an instruction entry and memory reference entries.
*/
static dr_emit_flags_t
event_app_instruction(void *drcontext, void *tag, instrlist_t *bb, instr_t *where,
                     bool for_trace, bool translating, void *user_data)
{
   int i;
   bool seen_memref = false;
   instru_data_t *data = (instru_data_t *)user_data;

   /* If the previous instruction was a write, we should handle it. */
   if (data->reg_addr != DR_REG_NULL)
       handle_post_write(drcontext, bb, where, data->reg_addr);
   data->reg_addr = DR_REG_NULL;

   /* Use the drmgr_orig_app_instr_* interface to properly handle our own use
    * of drutil_expand_rep_string() and drx_expand_scatter_gather() (as well
    * as another client/library emulating the instruction stream).
    */
   instr_t *instr_fetch = drmgr_orig_app_instr_for_fetch(drcontext);
   if (instr_fetch != NULL)
       data->last_opcode = instr_get_opcode(instr_fetch);

   instr_t *instr_operands = drmgr_orig_app_instr_for_operands(drcontext);
   if (instr_operands != NULL && instr_writes_memory(instr_operands)) {
       DR_ASSERT(instr_is_app(instr_operands));
       DR_ASSERT(data->last_opcode != 0);
       /* XXX: See above, in handle_post_write(). To simplify the handling of registers,
        * we assume no instruction has multiple distinct memory destination operands.
        */
       for (i = 0; i < instr_num_dsts(instr_operands); ++i) {
           if (opnd_is_memory_reference(instr_get_dst(instr_operands, i))) {
               if (seen_memref) {
                   DR_ASSERT_MSG(false, "Found inst with multiple memory destinations");
                   break;
               }
               data->reg_addr = instrument_pre_write(drcontext, bb, where,
                                                     data->last_opcode, instr_operands,
                                                     instr_get_dst(instr_operands, i));
               seen_memref = true;
           }
       }
   }

   if (drmgr_is_last_instr(drcontext, where))
       dr_thread_free(drcontext, data, sizeof(*data));
   return DR_EMIT_DEFAULT;
}

/* We transform string loops into regular loops so we can more easily
* monitor every memory reference they make.
*/
static dr_emit_flags_t
event_bb_app2app(void *drcontext, void *tag, instrlist_t *bb, bool for_trace,
                bool translating)
{
   if (!drutil_expand_rep_string(drcontext, bb)) {
       DR_ASSERT(false);
       /* in release build, carry on: we'll just miss per-iter refs */
   }
   if (!drx_expand_scatter_gather(drcontext, bb, NULL)) {
       DR_ASSERT(false);
   }
   drx_tail_pad_block(drcontext, bb);
   return DR_EMIT_DEFAULT;
}



static void
event_thread_init(void *drcontext)
{
    //initialize(32000000);
   per_thread_t *data = dr_thread_alloc(drcontext, sizeof(per_thread_t));
   DR_ASSERT(data != NULL);
   drmgr_set_tls_field(drcontext, tls_idx, data);

   /* We're going to dump our data to a per-thread file.
    * On Windows we need an absolute path so we place it in
    * the same directory as our library. We could also pass
    * in a path as a client argument.
    */
   data->log =
       log_file_open(client_id, drcontext, NULL /* using client lib path */, "memval",
#ifndef WINDOWS
                     DR_FILE_CLOSE_ON_FORK |
#endif
                         DR_FILE_ALLOW_LARGE);
   data->logf = log_stream_from_file(data->log);
}

static void
event_thread_exit(void *drcontext)
{
   per_thread_t *data = drmgr_get_tls_field(drcontext, tls_idx);
   log_stream_close(data->logf);
   dr_thread_free(drcontext, data, sizeof(per_thread_t));
}

static void
event_exit(void)
{
   if (!drmgr_unregister_tls_field(tls_idx) ||
       !drmgr_unregister_thread_init_event(event_thread_init) ||
       !drmgr_unregister_thread_exit_event(event_thread_exit) ||
       !drmgr_unregister_bb_app2app_event(event_bb_app2app) ||
       !drmgr_unregister_bb_insertion_event(event_app_instruction))
       DR_ASSERT(false);

   drx_buf_free(write_buffer);
   drx_buf_free(trace_buffer);
   drutil_exit();
   drreg_exit();
   drmgr_exit();
   drx_exit();
   drsym_exit();
}

/* Temp */
//static bool initialised = false;
/**
static struct handler_meta_d {
    const char *file_name;
    int sequence_number;
}handlerMetaD;
 **/
/**
static void initislise(){
    handlerMetaD.file_name = "/mnt/dax/test_outputs/mmaped_files/wrap_pmem_file__";
    handlerMetaD.sequence_number = 0;

    long pid;
    pid = (long)getpid();
    printf("Pid is: %ld \n", pid);
    criu_init_opts();
    criu_set_pid(pid);
    if(criu_set_service_address("../../crui_service/criu_service.socket")!=0){
        printf("Failed to set service address!\n");
    }

    int fd = open("criu_dump", O_DIRECTORY);
    criu_set_images_dir_fd(fd);
    criu_set_log_level(4);
    criu_set_leave_running(true);
    criu_set_log_file("restore.log");
    criu_set_shell_job(true);
    criu_set_ext_sharing(true);



}
**/
void create_unique_file_name(char *path_to_pmem){
    /**
    char sequence_number[sizeof (int)];
    sprintf(sequence_number, "%d",handlerMetaD.sequence_number);
    strcat(path_to_pmem, handlerMetaD.file_name);
    strcat(path_to_pmem, sequence_number);
    handlerMetaD.sequence_number++;
    return path_to_pmem;
     **/
    strcat(path_to_pmem, "/mnt/dax/test_outputs/mmaped_files/pmem_file");
}
/**
static void *create_and_map_persistent_memory_pool(){
    if(!initialised){
        initislise();
        initialised = true;
    }
    PMEMobjpool *popl;
    PMEMoid rootl;
    struct my_root *rootpl;

    char *path_to_pmem = calloc(200, 1);
    create_unique_file_name(path_to_pmem);

    if (file_exists((path_to_pmem)) != 0) {
        if ((popl = pmemobj_create(path_to_pmem, POBJ_LAYOUT_NAME(list),
                                  PMEMOBJ_MIN_POOL, 0666)) == NULL) {
            perror("failed to create pool\n");
        }
    } else {
        if ((popl = pmemobj_open(path_to_pmem, POBJ_LAYOUT_NAME(list))) == NULL) {
            perror("failed to open pool\n");
        }
    }
    rootl = pmemobj_root(pop, sizeof(struct my_root));
    rootpl = pmemobj_direct(root);
    return rootpl->this_is_on_pmem;
}
*/
/* End */

void sig_handler(int signum){
    printf("Handling signal \n");
    pmemobj_tx_abort(-1);
    exit(1);
}

DR_EXPORT void
dr_client_main(client_id_t id, int argc, const char *argv[])
{
    /* */
    //initialize(64000000);
    /* Handles cases for both programs */
    signal(SIGUSR1,sig_handler);

   drreg_options_t ops = { sizeof(ops), 4 /*max slots needed*/, false };
   dr_set_client_name("DynamoRIO Sample Client 'memval'", "http://dynamorio.org/issues");
   ;
   drsym_init(0);
   if (!drmgr_init() || !drutil_init() || !drx_init() || !drwrap_init())
       DR_ASSERT(false);
   if (drreg_init(&ops) != DRREG_SUCCESS)
       DR_ASSERT(false);

   /* register events */
   dr_register_exit_event(event_exit);

   if (!drmgr_register_module_load_event(module_load_event) ||
       !drmgr_register_thread_init_event(event_thread_init) ||
       !drmgr_register_thread_exit_event(event_thread_exit) ||
       !drmgr_register_bb_app2app_event(event_bb_app2app, NULL) ||
       !drmgr_register_bb_instrumentation_event(event_app_analysis,
                                                event_app_instruction, NULL))
       DR_ASSERT(false);
   client_id = id;
   tls_idx = drmgr_register_tls_field();
   trace_buffer = drx_buf_create_trace_buffer(MEM_BUF_SIZE, trace_fault);
   /* We could make this a trace buffer and specially handle faults, but it is not yet
    * worth the effort.
    */
   write_buffer = drx_buf_create_circular_buffer(WRT_BUF_SIZE);
   DR_ASSERT(tls_idx != -1 && trace_buffer != NULL && write_buffer != NULL);

   /* make it easy to tell, by looking at log file, which client executed */
   dr_log(NULL, DR_LOG_ALL, 1, "Client 'memval' initializing\n");
}