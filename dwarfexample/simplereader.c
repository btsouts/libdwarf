/*
  Copyright (c) 2009-2016 David Anderson.  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:
  * Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.
  * Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.
  * Neither the name of the example nor the
    names of its contributors may be used to endorse or promote products
    derived from this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY David Anderson ''AS IS'' AND ANY
  EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  DISCLAIMED. IN NO EVENT SHALL David Anderson BE LIABLE FOR ANY
  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
  (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*/
/*  simplereader.c
    This is an example of code reading dwarf .debug_info.
    It is kept simple to expose essential features.
    Though it now has a bunch of special options to enable
    testing of specific libdwarf features so it's no longer
    all that simple...

    It does not do all possible error reporting or error handling.
    It does to a bit of error checking as a help in ensuring
    that some code works properly... for error checks.

    The --names
    option adds some extra printing.

    The --check
    option does some interface and error checking.

    Option new September 2016:
        --dumpallnames=filepath
    This causes all the strings from the .debug_info and .debug_types
    sections to be written to 'filepath'. Any previous contents
    of the file are wiped out.
    This could be handy if you want to use the set of strings to
    investigate ways to improve the density of strings in some way.

    Options new 03 May 2015:
    These options do something different.
    They use specific DWARF5 package file libdwarf operations
    as a way to ensure libdwarf works properly (these
    specials used by the libdwarf regresson test suite).
    Examples given assuming dwp object fissionb-ld-new.dwp
    from the regressiontests
        --tuhash=hashvalue
        example: --tuhash=b0dd19898e8aa823
        It prints a DIE.

        --cuhash=hashvalue
        example: --cuhash=1e9983f631642b1a
        It prints a DIE.

        --cufissionhash=hashvalue
        example: --tufissionhash=1e9983f631642b1a
        It prints the fission data for this hash.

        --tufissionhash=hashvalue
        example: --tufissionhash=b0dd19898e8aa823
        It prints the fission data for this hash.

        --fissionfordie=cunumber
        example: --fissionfordie=5
        For CU number 5 (0 is the initial CU/TU)
        it accesses the CU/TU DIE and then
        uses that DIE to get the fission data.

    To use, try
        make
        ./simplereader simplereader
*/
#include "config.h"

/* Windows specific header files */
#ifdef HAVE_STDAFX_H
#include "stdafx.h"
#endif /* HAVE_STDAFX_H */

#include <sys/types.h> /* For open() */
#include <sys/stat.h>  /* For open() */
#include <fcntl.h>     /* For open() */
#include <stdlib.h>     /* For exit() */
#if HAVE_UNISTD_H
#include <unistd.h>     /* For close() */
#endif
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include "dwarf.h"
#include "libdwarf.h"
#ifdef _MSC_VER
#include <stdint.h>
#include <io.h>
#endif

#include "../dwarfdump/naming.h"
#include "../dwarfdump/helpertree.h"

/* Used to try to avoid leakage when we hide errors. */
#define DROP_ERROR_INSTANCE(d,r,e)       \
    if (r == DW_DLV_ERROR) {             \
        dwarf_dealloc(d,e,DW_DLA_ERROR); \
        e = 0;                           \
    }

struct srcfilesdata {
    char ** srcfiles;
    Dwarf_Signed srcfilescount;
    int srcfilesres;
};

typedef const char *(*encoding_type_func) (unsigned,int doprintingonerr);

static int pd_dwarf_names_print_on_error = 1;

#define TRUE 1
#define FALSE 0
#define FAILED -1

#define esb_append strcat

#define GLFLAGS_SHOW_GLOBAL_OFFSETS 1       // glflags.gf_show_global_offsets
#define GLFLAGS_CHECK_TYPE_OFFSET 1         // glflags.gf_check_type_offset
#define GLFLAGS_USE_OLD_DWARF_LOCLIST 0     // glflags.gf_use_old_dwarf_loclist

static void read_cu_list(Dwarf_Debug dbg);
static void print_die_data(Dwarf_Debug dbg, Dwarf_Die print_me,
    int level,
    struct srcfilesdata *sf);
static void get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die,
    int is_info, int in_level,
    struct srcfilesdata *sf);
static void resetsrcfiles(Dwarf_Debug dbg,struct srcfilesdata *sf);

static int
print_attribute(Dwarf_Debug dbg, Dwarf_Die die,
    Dwarf_Off dieprint_cu_goffset,
    Dwarf_Half attr,
    Dwarf_Attribute attr_in,
    int print_information,
    int die_indent_level,
    char **srcfiles, Dwarf_Signed cnt);

static void
print_error_maybe_continue(Dwarf_Debug dbg,
    const char * msg,
    int dwarf_code,
    Dwarf_Error lerr,
    Dwarf_Bool do_continue);

static void
print_error(Dwarf_Debug dbg,
    const char * msg,
    int dwarf_code,
    Dwarf_Error lerr);

static int
get_small_encoding_integer_and_name(Dwarf_Debug dbg,
    Dwarf_Attribute attrib,
    Dwarf_Unsigned * uval_out,
    const char *attr_name,
    char* string_out,
    encoding_type_func val_as_string,
    Dwarf_Error * seierr,
    int show_form);

static void
bracket_hex(const char *s1,
    Dwarf_Unsigned v,
    const char *s2,
    char * esbp);

static void
formx_unsigned(Dwarf_Unsigned u, char *esbp, Dwarf_Bool hex_format);    

static Dwarf_Bool
form_refers_local_info(Dwarf_Half form);

static int
formxdata_print_value(Dwarf_Debug dbg,
    Dwarf_Die die,
    Dwarf_Attribute attrib,
    char *esbp,
    Dwarf_Error * pverr, Dwarf_Bool hex_format);

static void
formx_unsigned_and_signed_if_neg(Dwarf_Unsigned tempud,
    Dwarf_Signed tempd,
    const char *leader, Dwarf_Bool hex_format, char *esbp);

static void
print_exprloc_content(Dwarf_Debug dbg,Dwarf_Die die,
    Dwarf_Attribute attrib,
    int showhextoo, char *esbp);    

static void
show_form_itself(int local_show_form,
    int local_verbose,
    int theform,
    int directform, char *esbp);

static int
check_for_type_unsigned(Dwarf_Debug dbg,
    Dwarf_Die die,
    char *esbp);

static char *
get_form_number_as_string(int form, char *buf, unsigned bufsize);

static void
formx_signed(Dwarf_Signed s, char *esbp);

void
get_string_from_locs(Dwarf_Debug dbg,
    Dwarf_Ptr bytes_in,
    Dwarf_Unsigned block_len,
    Dwarf_Half addr_size,
    Dwarf_Half offset_size,
    Dwarf_Half version,
    char *out_string);

void
dwarfdump_print_one_locdesc(Dwarf_Debug dbg,
    Dwarf_Locdesc * llbuf, /* Non-zero for old interface. */
    Dwarf_Locdesc_c locdesc,  /* Non-zero for 2015 interface. */
    Dwarf_Unsigned llent, /* Which desc we have . */
    Dwarf_Unsigned entrycount, /* How many location operators (DW_OP)? */
    Dwarf_Addr  baseaddr,
    char *string_out);

int
_dwarf_print_one_expr_op(Dwarf_Debug dbg,
    Dwarf_Loc* expr,
    Dwarf_Locdesc_c exprc,
    int index,
    Dwarf_Addr baseaddr,
    char *string_out);

static int
op_has_no_operands(int op);

static void
show_contents(char *string_out,
    unsigned int length,const unsigned char * bp);

/*  Use a generic call to open the file, due to issues with Windows */
int open_a_file(const char * name);
void close_a_file(int f);

static int namesoptionon = 0;
static int checkoptionon = 0;
static int dumpallnames = 0;
FILE *dumpallnamesfile = 0;
static const  char * dumpallnamespath = 0;
#if 0
DW_UT_compile                   0x01  /* DWARF5 */
DW_UT_type                      0x02  /* DWARF5 */
DW_UT_partial                   0x03  /* DWARF5 */
#endif

static int stdrun = TRUE;

static int unittype      = DW_UT_compile;
static Dwarf_Bool g_is_info = TRUE;

int cu_version_stamp = 0;
int cu_offset_size = 0;

/*  dienumberr is used to count DIEs.
    The point is to match fissionfordie. */
static int dienumber = 0;
static int fissionfordie = -1;
static int passnullerror = 0;
/*  These hash representations have to be converted to Dwarf_Sig8
    before use. */
static const  char * cuhash = 0;
static const  char * tuhash = 0;
static const  char * cufissionhash = 0;
static const  char * tufissionhash = 0;

/*  So we get clean reports from valgrind and other tools
    we clean up strdup strings.
    With a primitive technique as we need nothing fancy. */
#define DUPSTRARRAYSIZE 100
static const char *dupstrarray[DUPSTRARRAYSIZE];
static unsigned    dupstrused;

struct operation_descr_s {
    int op_code;
    int op_count;
    const char * op_1type;
};
struct operation_descr_s opdesc[]= {
    {DW_OP_addr,1,"addr" },
    {DW_OP_deref,0,"" },
    {DW_OP_const1u,1,"1u" },
    {DW_OP_const1s,1,"1s" },
    {DW_OP_const2u,1,"2u" },
    {DW_OP_const2s,1,"2s" },
    {DW_OP_const4u,1,"4u" },
    {DW_OP_const4s,1,"4s" },
    {DW_OP_const8u,1,"8u" },
    {DW_OP_const8s,1,"8s" },
    {DW_OP_constu,1,"uleb" },
    {DW_OP_consts,1,"sleb" },
    {DW_OP_dup,0,""},
    {DW_OP_drop,0,""},
    {DW_OP_over,0,""},
    {DW_OP_pick,1,"1u"},
    {DW_OP_swap,0,""},
    {DW_OP_rot,0,""},
    {DW_OP_xderef,0,""},
    {DW_OP_abs,0,""},
    {DW_OP_and,0,""},
    {DW_OP_div,0,""},
    {DW_OP_minus,0,""},
    {DW_OP_mod,0,""},
    {DW_OP_mul,0,""},
    {DW_OP_neg,0,""},
    {DW_OP_not,0,""},
    {DW_OP_or,0,""},
    {DW_OP_plus,0,""},
    {DW_OP_plus_uconst,1,"uleb"},
    {DW_OP_shl,0,""},
    {DW_OP_shr,0,""},
    {DW_OP_shra,0,""},
    {DW_OP_xor,0,""},
    {DW_OP_skip,1,"2s"},
    {DW_OP_bra,1,"2s"},
    {DW_OP_eq,0,""},
    {DW_OP_ge,0,""},
    {DW_OP_gt,0,""},
    {DW_OP_le,0,""},
    {DW_OP_lt,0,""},
    {DW_OP_ne,0,""},
    /* lit0 thru reg31 handled specially, no operands */
    /* breg0 thru breg31 handled specially, 1 operand */
    {DW_OP_regx,1,"uleb"},
    {DW_OP_fbreg,1,"sleb"},
    {DW_OP_bregx,2,"uleb"},
    {DW_OP_piece,1,"uleb"},
    {DW_OP_deref_size,1,"1u"},
    {DW_OP_xderef_size,1,"1u"},
    {DW_OP_nop,0,""},
    {DW_OP_push_object_address,0,""},
    {DW_OP_call2,1,"2u"},
    {DW_OP_call4,1,"4u"},
    {DW_OP_call_ref,1,"off"},
    {DW_OP_form_tls_address,0,""},
    {DW_OP_call_frame_cfa,0,""},
    {DW_OP_bit_piece,2,"uleb"},
    {DW_OP_implicit_value,2,"u"},
    {DW_OP_stack_value,0,""},
    {DW_OP_GNU_uninit,0,""},
    {DW_OP_GNU_encoded_addr,1,"addr"},
    {DW_OP_implicit_pointer,2,"addr" }, /* DWARF5 */
    {DW_OP_GNU_implicit_pointer,2,"addr" },
    {DW_OP_entry_value,2,"val" }, /* DWARF5 */
    {DW_OP_GNU_entry_value,2,"val" },
    {DW_OP_const_type,3,"uleb" }, /* DWARF5 */
    {DW_OP_GNU_const_type,3,"uleb" },
    {DW_OP_regval_type,2,"uleb" }, /* DWARF5 */
    {DW_OP_GNU_regval_type,2,"uleb" },
    {DW_OP_deref_type,1,"val" }, /* DWARF5 */
    {DW_OP_GNU_deref_type,1,"val" },
    {DW_OP_convert,1,"uleb" }, /* DWARF5 */
    {DW_OP_GNU_convert,1,"uleb" },
    {DW_OP_reinterpret,1,"uleb" }, /* DWARF5 */
    {DW_OP_GNU_reinterpret,1,"uleb" },

    {DW_OP_GNU_parameter_ref,1,"val" },
    {DW_OP_GNU_const_index,1,"val" },
    {DW_OP_GNU_push_tls_address,0,"" },

    {DW_OP_addrx,1,"uleb" }, /* DWARF5 */
    {DW_OP_GNU_addr_index,1,"val" },
    {DW_OP_constx,1,"u" }, /* DWARF5 */
    {DW_OP_GNU_const_index,1,"u" },

    {DW_OP_GNU_parameter_ref,1,"u" },

    {DW_OP_xderef,0,"" }, /* DWARF5 */
    {DW_OP_xderef_type,2,"1u" }, /* DWARF5 */
    /* terminator */
    {0,0,""}
};

static void
cleanupstr(void)
{
    unsigned i = 0;
    for (i = 0; i < dupstrused; ++i) {
        free((char *)dupstrarray[i]);
        dupstrarray[i] = 0;
    }
    dupstrused = 0;
}

static unsigned  char_to_uns4bit(unsigned char c)
{
    unsigned v;
    if( c >= '0' && c <= '9') {
        v =  c - '0';
    }
    else if( c >= 'a' && c <= 'f') {
        v =  c - 'a' + 10;
    }
    else if( c >= 'A' && c <= 'F') {
        v =  c - 'A' + 10;
    } else {
        printf("Garbage hex char in %c 0x%x\n",c,c);
        exit(1);
    }
    return v;
}

static void
xfrm_to_sig8(const char *cuhash_in, Dwarf_Sig8 *hash_out)
{
    char localhash[16];
    unsigned hashin_len = strlen(cuhash_in);
    unsigned fixed_size = sizeof(localhash);
    unsigned init_byte = 0;
    unsigned i;

    memset(localhash,0,fixed_size);
    if (hashin_len > fixed_size) {
        printf("FAIL: argument hash too long, len %u val:\"%s\"\n",hashin_len,
            cuhash_in);
        exit(1);
    }
    if (hashin_len  < fixed_size) {
        unsigned add_zeros = fixed_size - hashin_len;
        for ( ; add_zeros > 0; add_zeros--) {
            localhash[init_byte] = '0';
            init_byte++;
        }
    }
    for (i = 0; i < hashin_len; ++i,++init_byte) {
        localhash[init_byte] = cuhash_in[i];
    }

    /*  So now local hash as a full 16 bytes of hex characters with
        any needed leading zeros.
        transform it to 8 byte hex signature */

    for (i = 0; i < sizeof(Dwarf_Sig8) ; ++i) {
        unsigned char hichar = localhash[2*i];
        unsigned char lochar = localhash[2*i+1];
        hash_out->signature[i] =
            (char_to_uns4bit(hichar) << 4)  |
            char_to_uns4bit(lochar);
    }
    printf("Hex key = 0x");
    for (i = 0; i < sizeof(Dwarf_Sig8) ; ++i) {
        unsigned char c = hash_out->signature[i];
        printf("%02x",c);
    }
    printf("\n");
}

static int
startswithextractnum(const char *arg,const char *lookfor, int *numout)
{
    const char *s = 0;
    unsigned prefixlen = strlen(lookfor);
    int v = 0;
    if(strncmp(arg,lookfor,prefixlen)) {
        return FALSE;
    }
    s = arg+prefixlen;
    /*  We are not making any attempt to deal with garbage.
        Pass in good data... */
    v = atoi(s);
    *numout = v;
    return TRUE;
}

static int
startswithextractstring(const char *arg,const char *lookfor,
    const char ** ptrout)
{
    const char *s = 0;
    unsigned prefixlen = strlen(lookfor);
    if(strncmp(arg,lookfor,prefixlen)) {
        return FALSE;
    }
    s = arg+prefixlen;
    *ptrout = strdup(s);
    dupstrarray[dupstrused] = *ptrout;
    dupstrused++;
    if (dupstrused >= DUPSTRARRAYSIZE) {
        printf("FAIL: increase the value DUPSTRARRAYSIZE for test purposes\n");
        exit(1);
    }
    return TRUE;
}

static void
format_sig8_string(Dwarf_Sig8*data, char* str_buf,unsigned
  buf_size)
{
    unsigned i = 0;
    char *cp = str_buf;
    if (buf_size <  19) {
        printf("FAIL: internal coding error in test.\n");
        exit(1);
    }
    strcpy(cp,"0x");
    cp += 2;
    buf_size -= 2;
    for (; i < sizeof(data->signature); ++i,cp+=2,buf_size--) {
        snprintf(cp, buf_size, "%02x",
            (unsigned char)(data->signature[i]));
    }
    return;
}

static void
print_debug_fission_header(struct Dwarf_Debug_Fission_Per_CU_s *fsd)
{
    const char * fissionsec = ".debug_cu_index";
    unsigned i  = 0;
    char str_buf[30];

    if (!fsd || !fsd->pcu_type) {
        /* No fission data. */
        return;
    }
    printf("\n");
    if (!strcmp(fsd->pcu_type,"tu")) {
        fissionsec = ".debug_tu_index";
    }
    printf("  %-19s = %s\n","Fission section",fissionsec);
    printf("  %-19s = 0x%"  DW_PR_XZEROS DW_PR_DUx "\n","Fission index ",
        fsd->pcu_index);
    format_sig8_string(&fsd->pcu_hash,str_buf,sizeof(str_buf));
    printf("  %-19s = %s\n","Fission hash",str_buf);
    /* 0 is always unused. Skip it. */
    printf("  %-19s = %s\n","Fission entries","offset     size        DW_SECTn");
    for( i = 1; i < DW_FISSION_SECT_COUNT; ++i)  {
        const char *nstring = 0;
        Dwarf_Unsigned off = 0;
        Dwarf_Unsigned size = fsd->pcu_size[i];
        int res = 0;
        if (size == 0) {
            continue;
        }
        res = dwarf_get_SECT_name(i,&nstring);
        if (res != DW_DLV_OK) {
            nstring = "Unknown SECT";
        }
        off = fsd->pcu_offset[i];
        printf("  %-19s = 0x%08llx 0x%08llx %2u\n",
            nstring,
            off,size,i);
    }
}

/*  If there is no 'error' passed into a dwarf function
    and there is an error, and an error-handler like this
    is passed.  This example simply returns so we
    test how well that action works.  */
static void
simple_error_handler(Dwarf_Error error, Dwarf_Ptr errarg)
{
    Dwarf_Unsigned unused =  (Dwarf_Unsigned)errarg;
    printf("\nlibdwarf error detected: 0x%" DW_PR_DUx " %s\n",
        dwarf_errno(error),dwarf_errmsg(error));
    printf("libdwarf errarg. Not really used here %" DW_PR_DUu "\n",
        unused);
    return;
}


int
main(int argc, char **argv)
{
    Dwarf_Debug dbg = 0;
    int fd = -1;
    const char *filepath = "<stdin>";
    int res = DW_DLV_ERROR;
    Dwarf_Error error;
    Dwarf_Handler errhand = 0;
    Dwarf_Ptr errarg = 0;
    Dwarf_Sig8 hash8;
    Dwarf_Error *errp  = 0;
    int simpleerrhand = 0;

    if(argc < 2) {
        fd = 0; /* stdin */
    } else {
        int i = 0;
        for(i = 1; i < (argc-1) ; ++i) {
            if(strcmp(argv[i],"--names") == 0) {
                namesoptionon=1;
            } else if(startswithextractstring(argv[1],"--dumpallnames=",
                &dumpallnamespath)) {
                dumpallnames=1;
            } else if(strcmp(argv[i],"--check") == 0) {
                checkoptionon=1;
            } else if(startswithextractstring(argv[i],"--tuhash=",&tuhash)) {
                /* done */
            } else if(startswithextractstring(argv[i],"--cuhash=",&cuhash)) {
                /* done */
            } else if(startswithextractstring(argv[i],"--tufissionhash=",
                &tufissionhash)) {
                /* done */
            } else if(startswithextractstring(argv[i],"--cufissionhash=",
                &cufissionhash)) {
                /* done */
            } else if(strcmp(argv[i],"--passnullerror") == 0) {
                passnullerror=1;
            } else if(strcmp(argv[i],"--simpleerrhand") == 0) {
                simpleerrhand=1;
            } else if(startswithextractnum(argv[i],"--isinfo=",&g_is_info)) {
                /* done */
            } else if(startswithextractnum(argv[i],"--type=",&unittype)) {
                /* done */
            } else if(startswithextractnum(argv[i],"--fissionfordie=",
                &fissionfordie)) {
                /* done */
            } else {
                printf("Unknown argument \"%s\", give up \n",argv[i]);
                exit(1);
            }
        }
        filepath = argv[i];
        if (dumpallnames) {
            if (!strcmp(dumpallnamespath,filepath)) {
                printf("Using --dumpallnames with the same path  "
                    "(%s) "
                    "as the file to read is not allowed. giving up.\n",
                    filepath);
                exit(1);
            }
            dumpallnamesfile = fopen(dumpallnamespath,"w");
            if(!dumpallnamesfile) {
                printf("Cannot open %s. Giving up.\n",
                    dumpallnamespath);
                exit(1);
            }
        }
        fd = open_a_file(filepath);
    }
    if(argc > 2) {
    }
    if(fd < 0) {
        printf("Failure attempting to open \"%s\"\n",filepath);
    }
    if(passnullerror) {
        errp = 0;
    } else {
        errp = &error;
    }
    if (simpleerrhand) {
        errhand = simple_error_handler;
        /* Not a very useful errarg... */
        errarg = (Dwarf_Ptr)1;
    }
    res = dwarf_init(fd,DW_DLC_READ,errhand,errarg, &dbg,errp);
    if(res != DW_DLV_OK) {
        printf("Giving up, cannot do DWARF processing\n");
        cleanupstr();
        exit(1);
    }

    if(cuhash) {
        Dwarf_Die die;
        stdrun = FALSE;
        xfrm_to_sig8(cuhash,&hash8);
        printf("\n");
        printf("Getting die for CU key %s\n",cuhash);
        res = dwarf_die_from_hash_signature(dbg,
            &hash8,"cu",
            &die,errp);
        if (res == DW_DLV_OK) {
            struct srcfilesdata sf;
            printf("Hash found.\n");
            sf.srcfilesres = DW_DLV_ERROR;
            sf.srcfiles = 0;
            sf.srcfilescount = 0;
            print_die_data(dbg,die,0,&sf);
            dwarf_dealloc(dbg,die, DW_DLA_DIE);
        } else if (res == DW_DLV_NO_ENTRY) {
            printf("cuhash DW_DLV_NO_ENTRY.\n");
        } else { /* DW_DLV_ERROR */
            printf("cuhash DW_DLV_ERROR %s\n",
                errp? dwarf_errmsg(error):"an error");
        }
    }
    if(tuhash) {
        Dwarf_Die die;
        stdrun = FALSE;
        xfrm_to_sig8(tuhash,&hash8);
        printf("\n");
        printf("Getting die for TU key %s\n",tuhash);
        res = dwarf_die_from_hash_signature(dbg,
            &hash8,"tu",
            &die,errp);
        if (res == DW_DLV_OK) {
            struct srcfilesdata sf;
            printf("Hash found.\n");
            sf.srcfilesres = DW_DLV_ERROR;
            sf.srcfiles = 0;
            sf.srcfilescount = 0;
            print_die_data(dbg,die,0,&sf);
            dwarf_dealloc(dbg,die, DW_DLA_DIE);
        } else if (res == DW_DLV_NO_ENTRY) {
            printf("tuhash DW_DLV_NO_ENTRY.\n");
        } else { /* DW_DLV_ERROR */
            printf("tuhash DW_DLV_ERROR %s\n",
                errp?dwarf_errmsg(error):"error!");
        }

    }
    if(cufissionhash) {
        Dwarf_Debug_Fission_Per_CU  fisdata;
        stdrun = FALSE;
        memset(&fisdata,0,sizeof(fisdata));
        xfrm_to_sig8(cufissionhash,&hash8);
        printf("\n");
        printf("Getting fission data for CU key %s\n",cufissionhash);
        res = dwarf_get_debugfission_for_key(dbg,
            &hash8,"cu",
            &fisdata,errp);
        if (res == DW_DLV_OK) {
            printf("Hash found.\n");
            print_debug_fission_header(&fisdata);
        } else if (res == DW_DLV_NO_ENTRY) {
            printf("cufissionhash DW_DLV_NO_ENTRY.\n");
        } else { /* DW_DLV_ERROR */
            printf("cufissionhash DW_DLV_ERROR %s\n",
                errp?dwarf_errmsg(error):"error...");
        }
    }
    if(tufissionhash) {
        Dwarf_Debug_Fission_Per_CU  fisdata;
        stdrun = FALSE;
        memset(&fisdata,0,sizeof(fisdata));
        xfrm_to_sig8(tufissionhash,&hash8);
        printf("\n");
        printf("Getting fission data for TU key %s\n",tufissionhash);
        res = dwarf_get_debugfission_for_key(dbg,
            &hash8,"tu",
            &fisdata,errp);
        if (res == DW_DLV_OK) {
            printf("Hash found.\n");
            print_debug_fission_header(&fisdata);
        } else if (res == DW_DLV_NO_ENTRY) {
            printf("tufissionhash DW_DLV_NO_ENTRY.\n");
        } else { /* DW_DLV_ERROR */
            printf("tufissionhash DW_DLV_ERROR %s\n",
                errp?dwarf_errmsg(error):" Some error");
        }
    }
    if (stdrun) {
        /* Here we are. */

        
        read_cu_list(dbg);
    }
    res = dwarf_finish(dbg,errp);
    if(res != DW_DLV_OK) {
        printf("dwarf_finish failed!\n");
    }
    if (dumpallnamesfile) {
        fclose(dumpallnamesfile);
    }
    close_a_file(fd);
    cleanupstr();
    return 0;
}

static void
read_cu_list(Dwarf_Debug dbg)
{
    Dwarf_Unsigned cu_header_length = 0;
    Dwarf_Unsigned abbrev_offset = 0;
    Dwarf_Half     address_size = 0;
    Dwarf_Half     version_stamp = 0;
    Dwarf_Half     offset_size = 0;
    Dwarf_Half     extension_size = 0;
    Dwarf_Sig8     signature;
    Dwarf_Unsigned typeoffset = 0;
    Dwarf_Unsigned next_cu_header = 0;
    Dwarf_Half     header_cu_type = unittype;
    Dwarf_Bool     is_info = g_is_info;
    Dwarf_Error error;
    int cu_number = 0;
    Dwarf_Error *errp  = 0;


    // for(;;++cu_number) {
    for(;cu_number<1;cu_number++) {    
        Dwarf_Die no_die = 0;
        Dwarf_Die cu_die = 0;
        int res = DW_DLV_ERROR;
        struct srcfilesdata sf;
        sf.srcfilesres = DW_DLV_ERROR;
        sf.srcfiles = 0;
        sf.srcfilescount = 0;
        memset(&signature,0, sizeof(signature));

        if(passnullerror) {
            errp = 0;
        } else {
            errp = &error;
        }
        res = dwarf_next_cu_header_d(dbg,is_info,&cu_header_length,
            &version_stamp, &abbrev_offset,
            &address_size, &offset_size,
            &extension_size,&signature,
            &typeoffset, &next_cu_header,
            &header_cu_type,errp);
        if(res == DW_DLV_ERROR) {
            char *em = errp?dwarf_errmsg(error):"An error next cu her";
            printf("Error in dwarf_next_cu_header: %s\n",em);
            exit(1);
        }
        if(res == DW_DLV_NO_ENTRY) {
            /* Done. */
            return;
        }
        cu_version_stamp = version_stamp;
        cu_offset_size   = offset_size;
        /* The CU will have a single sibling, a cu_die. */
        res = dwarf_siblingof_b(dbg,no_die,is_info,
            &cu_die,errp);
        if(res == DW_DLV_ERROR) {
            char *em = errp?dwarf_errmsg(error):"An error";
            printf("Error in dwarf_siblingof_b on CU die: %s\n",em);
            exit(1);
        }
        if(res == DW_DLV_NO_ENTRY) {
            /* Impossible case. */
            printf("no entry! in dwarf_siblingof on CU die \n");
            exit(1);
        }
        get_die_and_siblings(dbg,cu_die,is_info,0,&sf);
        dwarf_dealloc(dbg,cu_die,DW_DLA_DIE);
        resetsrcfiles(dbg,&sf);
    }
}

static void
get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die,
    int is_info,int in_level,
   struct srcfilesdata *sf)
{
    int res = DW_DLV_ERROR;
    Dwarf_Die cur_die=in_die;
    Dwarf_Die child = 0;
    Dwarf_Error error = 0;
    Dwarf_Error *errp = 0;

    if(passnullerror) {
        errp = 0;
    } else {
        errp = &error;
    }
    print_die_data(dbg,in_die,in_level,sf);

    for(;;) {
        Dwarf_Die sib_die = 0;
        res = dwarf_child(cur_die,&child,errp);
        if(res == DW_DLV_ERROR) {
            printf("Error in dwarf_child , level %d \n",in_level);
            exit(1);
        }
        if(res == DW_DLV_OK) {
            get_die_and_siblings(dbg,child,is_info,in_level+1,sf);
        }
        /* res == DW_DLV_NO_ENTRY */
        res = dwarf_siblingof_b(dbg,cur_die,is_info,&sib_die,errp);
        if(res == DW_DLV_ERROR) {
            char *em = errp?dwarf_errmsg(error):"Error siblingof_b";
            printf("Error in dwarf_siblingof_b , level %d :%s \n",
                in_level,em);
            exit(1);
        }
        if(res == DW_DLV_NO_ENTRY) {
            /* Done at this level. */
            break;
        }
        /* res == DW_DLV_OK */
        if(cur_die != in_die) {
            dwarf_dealloc(dbg,cur_die,DW_DLA_DIE);
        }
        cur_die = sib_die;
        print_die_data(dbg,cur_die,in_level,sf);
    }
    return;
}
static void
get_addr(Dwarf_Attribute attr,Dwarf_Addr *val)
{
    Dwarf_Error error = 0;
    int res;
    Dwarf_Addr uval = 0;
    Dwarf_Error *errp  = 0;

    if(passnullerror) {
        errp = 0;
    } else {
        errp = &error;
    }

    res = dwarf_formaddr(attr,&uval,errp);
    if(res == DW_DLV_OK) {
        *val = uval;
        return;
    }
    return;
}
static void
get_number(Dwarf_Attribute attr,Dwarf_Unsigned *val)
{
    Dwarf_Error error = 0;
    int res;
    Dwarf_Signed sval = 0;
    Dwarf_Unsigned uval = 0;
    Dwarf_Error *errp  = 0;

    if(passnullerror) {
        errp = 0;
    } else {
        errp = &error;
    }
    res = dwarf_formudata(attr,&uval,errp);
    if(res == DW_DLV_OK) {
        *val = uval;
        return;
    }
    res = dwarf_formsdata(attr,&sval,errp);
    if(res == DW_DLV_OK) {
        *val = sval;
        return;
    }
    return;
}
static void
print_subprog(Dwarf_Debug dbg,Dwarf_Die die,
    int level,
    struct srcfilesdata *sf,
    const char *name)
{
    int res;
    Dwarf_Error error = 0;
    Dwarf_Attribute *attrbuf = 0;
    Dwarf_Addr lowpc = 0;
    Dwarf_Addr highpc = 0;
    Dwarf_Signed attrcount = 0;
    Dwarf_Signed i;
    Dwarf_Unsigned filenum = 0;
    Dwarf_Unsigned linenum = 0;
    char *filename = 0;
    Dwarf_Error *errp = 0;

    if(passnullerror) {
        errp = 0;
    } else {
        errp = &error;
    }
    res = dwarf_attrlist(die,&attrbuf,&attrcount,errp);
    if(res != DW_DLV_OK) {
        return;
    }
    for(i = 0; i < attrcount ; ++i) {
        Dwarf_Half aform;
        res = dwarf_whatattr(attrbuf[i],&aform,errp);
        if(res == DW_DLV_OK) {
            if(aform == DW_AT_decl_file) {
                Dwarf_Signed filenum_s = 0;

                get_number(attrbuf[i],&filenum);
                filenum_s = filenum;
                /*  Would be good to evaluate filenum_s
                    sanity here, ensuring filenum_s-1 is sensible. */
                if((filenum > 0) && (sf->srcfilescount > (filenum_s-1))) {
                    filename = sf->srcfiles[filenum_s-1];
                }
            }
            if(aform == DW_AT_decl_line) {
                get_number(attrbuf[i],&linenum);
            }
            if(aform == DW_AT_low_pc) {
                get_addr(attrbuf[i],&lowpc);
            }
            if(aform == DW_AT_high_pc) {
                /*  This will FAIL with DWARF4 highpc form
                    of 'class constant'.  */
                get_addr(attrbuf[i],&highpc);
            }
        }
        dwarf_dealloc(dbg,attrbuf[i],DW_DLA_ATTR);
    }
    /*  Here let's test some alternative interfaces for high and low pc.
        We only do both dwarf_highpc and dwarf_highpcb_b as
        an error check. Do not do both yourself. */
    if(checkoptionon){
        int hres = 0;
        int hresb = 0;
        int lres = 0;
        Dwarf_Addr althipc = 0;
        Dwarf_Addr hipcoffset = 0;
        Dwarf_Addr althipcb = 0;
        Dwarf_Addr altlopc = 0;
        Dwarf_Half highform = 0;
        enum Dwarf_Form_Class highclass = 0;

        /*  Reusing errp before checking for err here is
            bogus. FIXME. */
        /*  Should work for DWARF 2/3 DW_AT_high_pc, and
            all high_pc where the FORM is DW_FORM_addr
            Avoid using this interface as of 2013. */
        hres  = dwarf_highpc(die,&althipc,errp);

        /* Should work for all DWARF DW_AT_high_pc.  */
        hresb = dwarf_highpc_b(die,&althipcb,&highform,&highclass,errp);

        lres = dwarf_lowpc(die,&altlopc,errp);
        printf("high_pc checking %s ",name);

        if (hres == DW_DLV_OK) {
            /* present, FORM addr */
            printf("highpc   0x%" DW_PR_XZEROS DW_PR_DUx " ",
                althipc);
        } else if (hres == DW_DLV_ERROR) {
            printf("dwarf_highpc() error not class address ");
        } else {
            /* absent */
        }
        if(hresb == DW_DLV_OK) {
            /* present, FORM addr or const. */
            if(highform == DW_FORM_addr) {
                printf("highpcb  0x%" DW_PR_XZEROS DW_PR_DUx " ",
                    althipcb);
            } else {
                if(lres == DW_DLV_OK) {
                    hipcoffset = althipcb;
                    althipcb = altlopc + hipcoffset;
                    printf("highpcb  0x%" DW_PR_XZEROS DW_PR_DUx " "
                        "highoff  0x%" DW_PR_XZEROS DW_PR_DUx " ",
                        althipcb,hipcoffset);
                } else {
                    printf("highoff  0x%" DW_PR_XZEROS DW_PR_DUx " ",
                        althipcb);
                }
            }
        } else if (hresb == DW_DLV_ERROR) {
            printf("dwarf_highpc_b() error!");
        } else {
            /* absent */
        }

        /* Should work for all DWARF DW_AT_low_pc */
        if (lres == DW_DLV_OK) {
            /* present, FORM addr. */
            printf("lowpc    0x%" DW_PR_XZEROS DW_PR_DUx " ",
                altlopc);
        } else if (lres == DW_DLV_ERROR) {
            printf("dwarf_lowpc() error!");
        } else {
            /* absent. */
        }
        printf("\n");



    }
    if(namesoptionon && (filenum || linenum)) {
        printf("<%3d> file: %" DW_PR_DUu " %s  line %"
            DW_PR_DUu "\n",level,filenum,filename?filename:"",linenum);
    }
    if(namesoptionon && lowpc) {
        printf("<%3d> low_pc : 0x%" DW_PR_DUx  "\n",
            level, (Dwarf_Unsigned)lowpc);
    }
    if(namesoptionon && highpc) {
        printf("<%3d> high_pc: 0x%" DW_PR_DUx  "\n",
            level, (Dwarf_Unsigned)highpc);
    }
    dwarf_dealloc(dbg,attrbuf,DW_DLA_LIST);
}

static void
print_comp_dir(Dwarf_Debug dbg,Dwarf_Die die,
    int level, struct srcfilesdata *sf)
{
    int res;
    Dwarf_Error error = 0;
    Dwarf_Attribute *attrbuf = 0;
    Dwarf_Signed attrcount = 0;
    Dwarf_Signed i;
    Dwarf_Error *errp = 0;

    if(passnullerror) {
        errp = 0;
    } else {
        errp = &error;
    }

    res = dwarf_attrlist(die,&attrbuf,&attrcount,errp);
    if(res != DW_DLV_OK) {
        return;
    }
    sf->srcfilesres = dwarf_srcfiles(die,&sf->srcfiles,&sf->srcfilescount,
        &error);
    for(i = 0; i < attrcount ; ++i) {
        Dwarf_Half aform;
        res = dwarf_whatattr(attrbuf[i],&aform,errp);
        if(res == DW_DLV_OK) {
            if(aform == DW_AT_comp_dir) {
                char *name = 0;
                res = dwarf_formstring(attrbuf[i],&name,errp);
                if(res == DW_DLV_OK) {
                    printf(    "<%3d> compilation directory : \"%s\"\n",
                        level,name);
                }
            }
            if(aform == DW_AT_stmt_list) {
                /* Offset of stmt list for this CU in .debug_line */
            }
        }
        dwarf_dealloc(dbg,attrbuf[i],DW_DLA_ATTR);
    }
    dwarf_dealloc(dbg,attrbuf,DW_DLA_LIST);
}

static void
resetsrcfiles(Dwarf_Debug dbg,struct srcfilesdata *sf)
{
    Dwarf_Signed sri = 0;
    for (sri = 0; sri < sf->srcfilescount; ++sri) {
        dwarf_dealloc(dbg, sf->srcfiles[sri], DW_DLA_STRING);
    }
    dwarf_dealloc(dbg, sf->srcfiles, DW_DLA_LIST);
    sf->srcfilesres = DW_DLV_ERROR;
    sf->srcfiles = 0;
    sf->srcfilescount = 0;
}

static void
print_single_string(Dwarf_Debug dbg, Dwarf_Die die,Dwarf_Half attrnum)
{
    int res = 0;
    Dwarf_Error error = 0;
    char * stringval = 0;

    res = dwarf_die_text(die,attrnum, &stringval,&error);
    if (res == DW_DLV_OK) {
        // fprintf(dumpallnamesfile,"%s\n",stringval);
        fprintf(stderr,"%s\n",stringval);
        dwarf_dealloc(dbg,stringval, DW_DLA_STRING);
    }
    return;
}


static void
print_name_strings_attr(Dwarf_Debug dbg, Dwarf_Die die,
    Dwarf_Attribute attr)
{
    int res = 0;
    Dwarf_Half attrnum = 0;
    Dwarf_Half finalform = 0;
    enum Dwarf_Form_Class cl = DW_FORM_CLASS_UNKNOWN;
    Dwarf_Error error = 0;

    res = dwarf_whatattr(attr,&attrnum,&error);
    if(res != DW_DLV_OK) {
        printf("Unable to get attr number");
        exit(1);
    }

    res = dwarf_whatform(attr,&finalform,&error);
    if(res != DW_DLV_OK) {
        printf("Unable to get attr form");
        exit(1);
    }

    cl = dwarf_get_form_class(cu_version_stamp,
        attrnum,cu_offset_size,finalform);

    if (cl != DW_FORM_CLASS_STRING) {
        return;
    }
    print_single_string(dbg,die,attrnum);
}

static void
printnamestrings(Dwarf_Debug dbg, Dwarf_Die die)
{
    Dwarf_Error error =0;
    Dwarf_Attribute *atlist = 0;
    Dwarf_Signed atcount = 0;
    Dwarf_Signed i = 0;
    int res = 0;

    res = dwarf_attrlist(die,&atlist, &atcount,&error);
    if (res != DW_DLV_OK) {
        return;
    }
    for (i = 0; i < atcount; ++i) {
        Dwarf_Attribute attr = atlist[i];
        // Use an empty attr to get a placeholder on
        // the attr list for this IRDie.
        print_name_strings_attr(dbg,die,attr);
    }
    dwarf_dealloc(dbg,atlist, DW_DLA_LIST);

}

// print_one_die(Dwarf_Debug dbg, Dwarf_Die die,
//     Dwarf_Off dieprint_cu_goffset,
//     boolean print_information,
//     int die_indent_level,
//     char **srcfiles, Dwarf_Signed cnt,
//     boolean ignore_die_stack)

static void
print_die_data_i(Dwarf_Debug dbg, Dwarf_Die print_me,
    int level,
    struct srcfilesdata *sf)
{
    char *name = 0;
    Dwarf_Error error = 0;
    Dwarf_Half tag = 0;
    const char *tagname = 0;
    int localname = 0;
    int res = 0;
    Dwarf_Error *errp = 0;
    Dwarf_Attribute attr = 0;
    Dwarf_Half formnum = 0;
    const char *formname = 0;
    
    Dwarf_Signed i = 0;
    Dwarf_Signed j = 0;
    Dwarf_Off offset = 0;
    Dwarf_Off overall_offset = 0;
    Dwarf_Signed atcnt = 0;
    Dwarf_Attribute *atlist = 0;
    int tres = 0;
    int ores = 0;
    int atres = 0;
    Dwarf_Error podie_err = 0;

    Dwarf_Off  DIE_offset = 0;            /* DIE offset in compile unit */
    Dwarf_Off  DIE_overall_offset = 0;    /* DIE offset in .debug_info */

    Dwarf_Off dieprint_cu_goffset = 0;

    if (passnullerror) {
        errp = 0;
    } else {
        errp = &error;
    }
    res = dwarf_diename(print_me,&name,errp);
    if(res == DW_DLV_ERROR) {
        printf("Error in dwarf_diename , level %d \n",level);
        exit(1);
    }
    if(res == DW_DLV_NO_ENTRY) {
        name = "<no DW_AT_name attr>";
        localname = 1;
    }
    res = dwarf_tag(print_me,&tag,errp);
    if(res != DW_DLV_OK) {
        printf("Error in dwarf_tag , level %d \n",level);
        exit(1);
    }
    res = dwarf_get_TAG_name(tag,&tagname);
    if(res != DW_DLV_OK) {
        printf("Error in dwarf_get_TAG_name , level %d \n",level);
        exit(1);
    }
    // if (dumpallnames) {
    //     printnamestrings(dbg,print_me);
    // }

    // printnamestrings(dbg,print_me);

    res = dwarf_attr(print_me,DW_AT_name,&attr, errp);
    if (res != DW_DLV_OK) {
        /* do nothing */
    } else {
        res = dwarf_whatform(attr,&formnum,errp);
        if (res != DW_DLV_OK) {
            printf("Error in dwarf_whatform , level %d \n",level);
            exit(1);
        }
        formname = "form-name-unavailable";
        res = dwarf_get_FORM_name(formnum,&formname);
        if (res != DW_DLV_OK) {
            formname = "UNKNoWn FORM!";
        }
        dwarf_dealloc(dbg,attr,DW_DLA_ATTR);
    }

    /* ---------- */

    atres = dwarf_attrlist(print_me, &atlist, &atcnt, &podie_err);

    if (atres == DW_DLV_ERROR) {
        print_error(dbg, "dwarf_attrlist", atres, podie_err);
    } else if (atres == DW_DLV_NO_ENTRY) {
        /* indicates there are no attrs.  It is not an error. */
        atcnt = 0;
    }

    /* Reset any loose references to low or high PC */
    // bSawLow = FALSE;
    // bSawHigh = FALSE;

    /* Get the offset for easy error reporting: This is not the CU die.  */
    dwarf_die_offsets(print_me,&DIE_overall_offset,&DIE_offset,&podie_err);

    for (i = 0; i < atcnt; i++) 
    {
        Dwarf_Half attr;
        int ares;

        ares = dwarf_whatattr(atlist[i], &attr, &podie_err);

        if (ares == DW_DLV_OK) {
            /*  Check duplicated attributes; use brute force as the number of
                attributes is quite small; the problem was detected with the
                LLVM toolchain, generating more than 12 repeated attributes */
            
            /* Print using indentation */

            int attr_match = print_attribute(dbg, print_me,
                dieprint_cu_goffset,
                attr,
                atlist[i],
                TRUE, level, NULL, 0);

            /*
             * print_information -> 1 - TRUE
             * srcfiles -> NULL
             * cnt -> 0
             */
            
        } 
        else
        { 
            print_error(dbg, "dwarf_whatattr entry missing", ares, podie_err);
        }
    }

    for (i = 0; i < atcnt; i++) {
        dwarf_dealloc(dbg, atlist[i], DW_DLA_ATTR);
    }

    if (atres == DW_DLV_OK) {
        dwarf_dealloc(dbg, atlist, DW_DLA_LIST);
    }

    if(namesoptionon ||checkoptionon) {
        if( tag == DW_TAG_subprogram) {
            if(namesoptionon) {
                printf(    "<%3d> subprogram            : \"%s\"\n",level,name);
            }
            print_subprog(dbg,print_me,level,sf,name);
        }
        if( (namesoptionon) && (tag == DW_TAG_compile_unit ||
            tag == DW_TAG_partial_unit ||
            tag == DW_TAG_type_unit)) {

            resetsrcfiles(dbg,sf);
            printf(    "<%3d> source file           : \"%s\"\n",level,name);
            print_comp_dir(dbg,print_me,level,sf);
        }
    } else {
        printf("<%d> tag: %d %s  name: \"%s\"",level,tag,tagname,name);
        if (formname) {
            printf(" FORM 0x%x \"%s\"",formnum, formname);
        }
        printf("\n");
    }
    if(!localname) {
        dwarf_dealloc(dbg,name,DW_DLA_STRING);
    }
}

static void
print_die_data(Dwarf_Debug dbg, Dwarf_Die print_me,
    int level,
    struct srcfilesdata *sf)
{

    if (fissionfordie != -1) {
        Dwarf_Debug_Fission_Per_CU percu;
        memset(&percu,0,sizeof(percu));
        if (fissionfordie == dienumber) {
            int res = 0;
            Dwarf_Error error = 0;
            Dwarf_Error *errp = 0;

            if (passnullerror) {
                errp = 0;
            } else {
                errp = &error;
            }
            res = dwarf_get_debugfission_for_die(print_me,
                &percu,errp);
            if(res == DW_DLV_ERROR) {
                printf("FAIL: Error in dwarf_diename  on fissionfordie %d\n",
                    fissionfordie);
                exit(1);
            }
            if(res == DW_DLV_NO_ENTRY) {
                printf("FAIL: no-entry in dwarf_diename  on fissionfordie %d\n",
                    fissionfordie);
                exit(1);
            }
            print_die_data_i(dbg,print_me,level,sf);
            print_debug_fission_header(&percu);
            exit(0);
        }
        dienumber++;
        return;
    }
    print_die_data_i(dbg,print_me,level,sf);
    dienumber++;
}

int
open_a_file(const char * name)
{
    /* Set to a file number that cannot be legal. */
    int f = -1;

#ifdef _MSC_VER
    f = _open(name, _O_RDONLY| _O_BINARY);
#elif defined(__CYGWIN__) || defined(WIN32)
    /*  It is not possible to share file handles
        between applications or DLLs. Each application has its own
        file-handle table. For two applications to use the same file
        using a DLL, they must both open the file individually.
        Let the 'libelf' dll to open and close the file.  */

    /* For WIN32 open the file as binary */
    f = elf_open(name, O_RDONLY | O_BINARY);
#else
    f = open(name, O_RDONLY);
#endif
    return f;
}

void
close_a_file(int f)
{
#ifdef _MSC_VER
    _close(f);
#else
    close(f);
#endif
}

static int
print_attribute(Dwarf_Debug dbg, Dwarf_Die die,
    Dwarf_Off dieprint_cu_goffset,
    Dwarf_Half attr,
    Dwarf_Attribute attr_in,
    int print_information,
    int die_indent_level,
    char **srcfiles, Dwarf_Signed cnt)
{
    Dwarf_Attribute attrib = 0;
    Dwarf_Unsigned uval = 0;
    const char * atname = 0;
    // struct esb_s valname;
    // struct esb_s esb_extra;
    int tres = 0;
    Dwarf_Half tag = 0;
    int append_extra_string = 0;
    // boolean found_search_attr = FALSE;
    // boolean bTextFound = FALSE;
    Dwarf_Bool is_info = FALSE;
    Dwarf_Addr elf_max_address = 0;
    Dwarf_Error paerr = 0;
    char attributeOut[256];

    // esb_constructor(&esb_extra);
    // esb_constructor(&valname);

    // is_info = dwarf_get_die_infotypes_flag(die);
    // atname = get_AT_name(attr,1);
    // get_address_size_and_max(dbg,0,&elf_max_address,&paerr);

    /*  The following gets the real attribute, even in the face of an
        incorrect doubling, or worse, of attributes. */
    attrib = attr_in;

    int vres;

    switch (attr) {
        case DW_AT_language:
            get_small_encoding_integer_and_name(dbg, attrib, &uval,
                "DW_AT_language", attributeOut,
                get_LANG_name, &paerr,
                0); //show_form_used

            // vres = dwarf_formudata(attrib, &uval, &paerr);

            printf("Found a DW_AT_language attribute: %s\n", attributeOut);
            
            break;
        case DW_AT_encoding:
            get_small_encoding_integer_and_name(dbg, attrib, &uval,
                "DW_AT_encoding", attributeOut,
                get_ATE_name, &paerr,
                0);
            
            printf("Found a DW_AT_encoding attribute: %s\n", attributeOut);
            
            break;
            /*  FALL THRU to location description */
        case DW_AT_location:
            printf("Found a DW_AT_location attribute\n");
            break;
        case DW_AT_vtable_elem_location:
            printf("Found a DW_AT_vtable_elem_location attribute\n");
            break;
        case DW_AT_string_length:
            printf("Found a DW_AT_string_length attribute\n");
            break;
        case DW_AT_return_addr:
            printf("Found a DW_AT_return_addr attribute\n");
            break;
        case DW_AT_use_location:
            printf("Found a DW_AT_use_location attribute\n");
            break;    
        case DW_AT_static_link:
            printf("Found a DW_AT_static_link attribute\n");
            break;
        case DW_AT_frame_base:
        {
            /*  The value is a location description
                or location list. */

            // struct esb_s framebasestr;
            // Dwarf_Half theform = 0;
            // Dwarf_Half directform = 0;

            // esb_constructor(&framebasestr);
            // get_form_values(dbg,attrib,&theform,&directform);
            // if (is_location_form(theform)) {
            //     get_location_list(dbg, die, attrib, &framebasestr);
            //     show_form_itself(show_form_used,verbose,
            //         theform, directform,&framebasestr);
            // } else if (theform == DW_FORM_exprloc)  {
            //     int showhextoo = 1;
            //     print_exprloc_content(dbg,die,attrib,showhextoo,&framebasestr);
            // } else {
            //     show_attr_form_error(dbg,attr,theform,&framebasestr);
            // }
            // esb_empty_string(&valname);
            // esb_append(&valname, esb_get_string(&framebasestr));
            // esb_destructor(&framebasestr);
        }
            printf("Found a DW_AT_frame_base attribute\n");
            
            break;
        case DW_AT_low_pc:
            printf("Found a DW_AT_low_pc attribute\n");
            break;
        case DW_AT_high_pc:
            printf("Found a DW_AT_high_pc attribute\n");
            break;
        case DW_AT_name:
            printf("Found a DW_AT_name attribute\n");
            break;
        case DW_AT_GNU_template_name:    
            printf("Found a DW_AT_GNU_template_name attribute\n");
            break;
        case DW_AT_producer:
            printf("Found a DW_AT_GNU_template_name attribute\n");
            break;
        case DW_AT_type:
            printf("Found a DW_AT_type attribute\n");
            break;    
        default:
            printf("Found untracked attribute: 0x%X\n", attr);
            break;
    }
}



static void
print_error_maybe_continue(Dwarf_Debug dbg,
    const char * msg,
    int dwarf_code,
    Dwarf_Error lerr,
    Dwarf_Bool do_continue)
{
    printf("\n");

    /*  FIXME   */
    const char * program_name = "aoua";

    if (dwarf_code == DW_DLV_ERROR) {
        char * errmsg = dwarf_errmsg(lerr);

        /*  We now (April 2016) guarantee the
            error number is in
            the error string so we do not need to print
            the dwarf_errno() value to show the number. */
        if (do_continue) {
            printf( "%s ERROR:  %s:  %s. Attempting to continue.\n",
                program_name, msg, errmsg);
        } else {
            printf( "%s ERROR:  %s:  %s\n",
                program_name, msg, errmsg);
        }
    } else if (dwarf_code == DW_DLV_NO_ENTRY) {
        printf("%s NO ENTRY:  %s: \n", program_name, msg);
    } else if (dwarf_code == DW_DLV_OK) {
        printf("%s:  %s \n", program_name, msg);
    } else {
        printf("%s InternalError:  %s:  code %d\n",
            program_name, msg, dwarf_code);
    }

    /* Display compile unit name */
    // PRINT_CU_INFO();
}

static void
print_error(Dwarf_Debug dbg,
    const char * msg,
    int dwarf_code,
    Dwarf_Error lerr)
{
    print_error_maybe_continue(dbg,msg,dwarf_code,lerr,FALSE);
    if (dbg) {
        Dwarf_Error ignored_err = 0;
        /*  If dbg was never initialized dwarf_finish
            can do nothing useful. There is no
            global-state for libdwarf to clean up. */
        if (dwarf_code == DW_DLV_ERROR) {
            dwarf_dealloc(dbg,lerr,DW_DLA_ERROR);
        }
        dwarf_finish(dbg, &ignored_err);
    }
    exit(FAILED);
}

static int
get_small_encoding_integer_and_name(Dwarf_Debug dbg,
    Dwarf_Attribute attrib,
    Dwarf_Unsigned * uval_out,
    const char *attr_name,
    char* string_out,
    encoding_type_func val_as_string,
    Dwarf_Error * seierr,
    int show_form)
{
    Dwarf_Unsigned uval = 0;
    int vres = dwarf_formudata(attrib, &uval, seierr);
    
    strcpy(string_out, val_as_string((Dwarf_Half) uval, pd_dwarf_names_print_on_error));

    return 0;   
}

void
get_attr_value(Dwarf_Debug dbg, Dwarf_Half tag,
    Dwarf_Die die,
    Dwarf_Off dieprint_cu_goffset,
    Dwarf_Attribute attrib,
    char **srcfiles, Dwarf_Signed cnt, char *esbp,
    int show_form,
    int local_verbose)
{
    Dwarf_Half theform = 0;
    char * temps = 0;
    Dwarf_Block *tempb = 0;
    Dwarf_Signed tempsd = 0;
    Dwarf_Unsigned tempud = 0;
    Dwarf_Off off = 0;
    Dwarf_Die die_for_check = 0;
    Dwarf_Half tag_for_check = 0;
    Dwarf_Bool tempbool = 0;
    Dwarf_Addr addr = 0;
    int fres = 0;
    int bres = 0;
    int wres = 0;
    int dres = 0;
    Dwarf_Half direct_form = 0;
    char small_buf[512];  /* Size to hold a filename COMPILE_UNIT_NAME_LEN */
    Dwarf_Bool is_info = TRUE;
    Dwarf_Error err = 0;


    is_info = dwarf_get_die_infotypes_flag(die);
    /*  Dwarf_whatform gets the real form, DW_FORM_indir is
        never returned: instead the real form following
        DW_FORM_indir is returned. */
    fres = dwarf_whatform(attrib, &theform, &err);
    /*  Depending on the form and the attribute, process the form. */
    if (fres == DW_DLV_ERROR) {
        print_error(dbg, "dwarf_whatform cannot Find Attr Form", fres,
            err);
    } else if (fres == DW_DLV_NO_ENTRY) {
        return;
    }
    /*  dwarf_whatform_direct gets the 'direct' form, so if
        the form is DW_FORM_indir that is what is returned. */
    dwarf_whatform_direct(attrib, &direct_form, &err);
    /*  Ignore errors in dwarf_whatform_direct() */

    switch (theform) {
    case DW_FORM_GNU_addr_index:
    case DW_FORM_addrx:
    case DW_FORM_addr:
        bres = dwarf_formaddr(attrib, &addr, &err);
        if (bres == DW_DLV_OK) {
            if (theform == DW_FORM_GNU_addr_index ||
                theform == DW_FORM_addrx) {
                Dwarf_Unsigned index = 0;
                int res = dwarf_get_debug_addr_index(attrib,&index,&err);
                if(res != DW_DLV_OK) {
                    print_error(dbg, "addr missing index ?!", res, err);
                }
                bracket_hex("(addr_index: ",index, ")",esbp);
            }
            bracket_hex("",addr,"",esbp);
        } else if (bres == DW_DLV_ERROR) {
            if (DW_DLE_MISSING_NEEDED_DEBUG_ADDR_SECTION ==
                dwarf_errno(err)) {
                Dwarf_Unsigned index = 0;
                int res = dwarf_get_debug_addr_index(attrib,&index,&err);
                if(res != DW_DLV_OK) {
                    print_error(dbg, "addr missing index ?!", bres, err);
                }

                addr = 0;
                bracket_hex("(addr_index: ",index,
                    ")<no .debug_addr section>",esbp);
                /*  This is normal in a .dwo file. The .debug_addr
                    is in a .o and in the final executable. */
            } else {
                print_error(dbg, "addr form with no addr?!", bres, err);
            }
        } else {
            print_error(dbg, "addr is a DW_DLV_NO_ENTRY? Impossible.",
                bres, err);
        }
        break;
    case DW_FORM_ref_addr:
        {
        Dwarf_Half attr = 0;
        /*  DW_FORM_ref_addr is not accessed thru formref: ** it is an
            address (global section offset) in ** the .debug_info
            section. */
        bres = dwarf_global_formref(attrib, &off, &err);
        if (bres == DW_DLV_OK) {
            bracket_hex("<GOFF=",off, ">",esbp);
        } else {
            print_error(dbg,
                "DW_FORM_ref_addr form with no reference?!",
                bres, err);
        }
        wres = dwarf_whatattr(attrib, &attr, &err);
        if (wres == DW_DLV_ERROR) {
        } else if (wres == DW_DLV_NO_ENTRY) {
        } else {
            if (attr == DW_AT_sibling) {
                /*  The value had better be inside the current CU
                    else there is a nasty error here, as a sibling
                    has to be in the same CU, it seems. */
                /*  The target offset (off) had better be
                    following the die's global offset else
                    we have a serious botch. this FORM
                    defines the value as a .debug_info
                    global offset. */
                Dwarf_Off cuoff = 0;
                Dwarf_Off culen = 0;
                Dwarf_Off die_overall_offset = 0;
                int res = 0;
                int ores = dwarf_dieoffset(die, &die_overall_offset, &err);
                if (ores != DW_DLV_OK) {
                    print_error(dbg, "dwarf_dieoffset", ores, err);
                }
                // SET_DIE_STACK_SIBLING(off);
                if (die_overall_offset >= off) {
                    snprintf(small_buf,sizeof(small_buf),
                        "ERROR: Sibling DW_FORM_ref_offset 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        " points %s die Global offset "
                        "0x%"  DW_PR_XZEROS  DW_PR_DUx,
                        off,(die_overall_offset == off)?"at":"before",
                        die_overall_offset);
                    print_error(dbg,small_buf,DW_DLV_OK,0);
                }

                res = dwarf_die_CU_offset_range(die,&cuoff,
                    &culen,&err);
                // DWARF_CHECK_COUNT(tag_tree_result,1);
                if (res != DW_DLV_OK) {
                } else {
                    Dwarf_Off cuend = cuoff+culen;
                    if (off <  cuoff || off >= cuend) {
                        // DWARF_CHECK_ERROR(tag_tree_result,
                        //     "DW_AT_sibling DW_FORM_ref_addr offset points "
                        //     "outside of current CU");
                    }
                }
            }
        }
        }

        break;
    case DW_FORM_ref1:
    case DW_FORM_ref2:
    case DW_FORM_ref4:
    case DW_FORM_ref8:
    case DW_FORM_ref_udata:
        {
        int refres = 0;
        Dwarf_Half attr = 0;
        Dwarf_Off goff = 0; /* Global offset */
        Dwarf_Error referr = 0;

        /* CU-relative offset returned. */
        refres = dwarf_formref(attrib, &off, &referr);
        if (refres != DW_DLV_OK) {
            /* Report incorrect offset */
            snprintf(small_buf,sizeof(small_buf),
                "%s, offset=<0x%"  DW_PR_XZEROS  DW_PR_DUx
                ">","reference form with no valid local ref?!",off);
            print_error(dbg, small_buf, refres, referr);
        }

        refres = dwarf_whatattr(attrib, &attr, &referr);
        if (refres != DW_DLV_OK) {
            snprintf(small_buf,sizeof(small_buf),
                "Form %d, has no attribute value?!" ,theform);
            print_error(dbg, small_buf, refres, referr);
        }

        /*  Convert the local offset 'off' into a global section
            offset 'goff'. */
        refres = dwarf_convert_to_global_offset(attrib,
            off, &goff, &referr);
        if (refres != DW_DLV_OK) {
            /*  Report incorrect offset */
            snprintf(small_buf,sizeof(small_buf),
                "%s, GOFF=<0x%"  DW_PR_XZEROS  DW_PR_DUx
                ">","invalid offset",goff);
            print_error(dbg, small_buf, refres, referr);
        }
        if (attr == DW_AT_sibling) {
            /*  The value had better be inside the current CU
                else there is a nasty error here, as a sibling
                has to be in the same CU, it seems. */
            /*  The target offset (off) had better be
                following the die's global offset else
                we have a serious botch. this FORM
                defines the value as a .debug_info
                global offset. */
            Dwarf_Off die_overall_offset = 0;
            int ores = dwarf_dieoffset(die, &die_overall_offset, &referr);
            if (ores != DW_DLV_OK) {
                print_error(dbg, "dwarf_dieoffset", ores, referr);
            }
            // SET_DIE_STACK_SIBLING(goff);
            if (die_overall_offset >= goff) {
                snprintf(small_buf,sizeof(small_buf),
                    "ERROR: Sibling offset 0x%"  DW_PR_XZEROS  DW_PR_DUx
                    " points %s its own die GOFF="
                    "0x%"  DW_PR_XZEROS  DW_PR_DUx,
                    goff,
                    (die_overall_offset == goff)?"at":"before",
                    die_overall_offset);
                print_error(dbg,small_buf,DW_DLV_OK,0);
            }

        }

        /*  Do references inside <> to distinguish them ** from
            constants. In dense form this results in <<>>. Ugly for
            dense form, but better than ambiguous. davea 9/94 */
        // if (glflags.gf_show_global_offsets) {
        if (GLFLAGS_SHOW_GLOBAL_OFFSETS) {    
            bracket_hex("<",off,"",esbp);
            bracket_hex(" GOFF=",goff,">",esbp);
        } else {
            bracket_hex("<",off,">",esbp);
        }

        // if (glflags.gf_check_type_offset) {
        if (GLFLAGS_CHECK_TYPE_OFFSET) {
            if (attr == DW_AT_type && form_refers_local_info(theform)) {
                dres = dwarf_offdie_b(dbg, goff,
                    is_info,
                    &die_for_check, &referr);
                if (dres != DW_DLV_OK) {
                    snprintf(small_buf,sizeof(small_buf),
                        "DW_AT_type offset does not point to a DIE "
                        "for global offset 0x%" DW_PR_XZEROS DW_PR_DUx
                        " cu off 0x%" DW_PR_XZEROS DW_PR_DUx
                        " local offset 0x%" DW_PR_XZEROS DW_PR_DUx
                        " tag 0x%x",
                        goff,dieprint_cu_goffset,off,tag);
                    // DWARF_CHECK_ERROR(type_offset_result,small_buf);
                } else {
                    int tres2 =
                        dwarf_tag(die_for_check, &tag_for_check, &err);
                    if (tres2 == DW_DLV_OK) {
                        switch (tag_for_check) {
                        case DW_TAG_array_type:
                        case DW_TAG_class_type:
                        case DW_TAG_enumeration_type:
                        case DW_TAG_pointer_type:
                        case DW_TAG_reference_type:
                        case DW_TAG_rvalue_reference_type:
                        case DW_TAG_restrict_type:
                        case DW_TAG_string_type:
                        case DW_TAG_structure_type:
                        case DW_TAG_subroutine_type:
                        case DW_TAG_typedef:
                        case DW_TAG_union_type:
                        case DW_TAG_ptr_to_member_type:
                        case DW_TAG_set_type:
                        case DW_TAG_subrange_type:
                        case DW_TAG_base_type:
                        case DW_TAG_const_type:
                        case DW_TAG_file_type:
                        case DW_TAG_packed_type:
                        case DW_TAG_thrown_type:
                        case DW_TAG_volatile_type:
                        case DW_TAG_template_type_parameter:
                        case DW_TAG_template_value_parameter:
                        case DW_TAG_unspecified_type:
                        /* Template alias */
                        case DW_TAG_template_alias:
                            /* OK */
                            break;
                        default:
                            {
                                snprintf(small_buf,sizeof(small_buf),
                                    "DW_AT_type offset "
                                    "0x%" DW_PR_XZEROS DW_PR_DUx
                                    " does not point to Type"
                                    " info we got tag 0x%x %s",
                                (Dwarf_Unsigned)goff,
                                tag_for_check,
                                get_TAG_name(tag_for_check,
                                    pd_dwarf_names_print_on_error));
                                // DWARF_CHECK_ERROR(type_offset_result,small_buf);
                            }
                            break;
                        }
                        dwarf_dealloc(dbg, die_for_check, DW_DLA_DIE);
                        die_for_check = 0;
                    } else {
                        // DWARF_CHECK_ERROR(type_offset_result,
                        //     "DW_AT_type offset does not exist");
                    }
                }
            }
        }
        }
        break;
    case DW_FORM_block:
    case DW_FORM_block1:
    case DW_FORM_block2:
    case DW_FORM_block4:
        fres = dwarf_formblock(attrib, &tempb, &err);
        if (fres == DW_DLV_OK) {
            unsigned u = 0;

            for (u = 0; u < tempb->bl_len; u++) {
                snprintf(small_buf, sizeof(small_buf), "%02x",
                    *(u + (unsigned char *) tempb->bl_data));
                esb_append(esbp, small_buf);
            }
            dwarf_dealloc(dbg, tempb, DW_DLA_BLOCK);
            tempb = 0;
        } else {
            print_error(dbg, "DW_FORM_blockn cannot get block\n", fres,
                err);
        }
        break;
    case DW_FORM_data1:
    case DW_FORM_data2:
    case DW_FORM_data4:
    case DW_FORM_data8:
        {
        Dwarf_Half attr = 0;
        fres = dwarf_whatattr(attrib, &attr, &err);
        if (fres == DW_DLV_ERROR) {
            print_error(dbg, "FORM_datan cannot get attr", fres, err);
        } else if (fres == DW_DLV_NO_ENTRY) {
            print_error(dbg, "FORM_datan cannot get attr", fres, err);
        } else {
            switch (attr) {
            case DW_AT_ordering:
            case DW_AT_byte_size:
            case DW_AT_bit_offset:
            case DW_AT_bit_size:
            case DW_AT_inline:
            case DW_AT_language:
            case DW_AT_visibility:
            case DW_AT_virtuality:
            case DW_AT_accessibility:
            case DW_AT_address_class:
            case DW_AT_calling_convention:
            case DW_AT_discr_list:      /* DWARF2 */
            case DW_AT_encoding:
            case DW_AT_identifier_case:
            case DW_AT_MIPS_loop_unroll_factor:
            case DW_AT_MIPS_software_pipeline_depth:
            case DW_AT_decl_column:
            case DW_AT_decl_file:
            case DW_AT_decl_line:
            case DW_AT_call_column:
            case DW_AT_call_file:
            case DW_AT_call_line:
            case DW_AT_start_scope:
            case DW_AT_byte_stride:
            case DW_AT_bit_stride:
            case DW_AT_count:
            case DW_AT_stmt_list:
            case DW_AT_MIPS_fde:
                
                break;
            case DW_AT_const_value:
                /* Do not use hexadecimal format */
                wres = formxdata_print_value(dbg,die,attrib,esbp, &err, FALSE);
                if (wres == DW_DLV_OK){
                    /* String appended already. */
                } else if (wres == DW_DLV_NO_ENTRY) {
                    /* nothing? */
                } else {
                    print_error(dbg,"Cannot get DW_AT_const_value ",wres,err);
                }
                break;
            case DW_AT_GNU_dwo_id:
            case DW_AT_dwo_id:
                
                break;
            case DW_AT_upper_bound:
            case DW_AT_lower_bound:
            default:  {
                Dwarf_Bool chex = FALSE;
                Dwarf_Die  tdie = die;
                if(DW_AT_ranges == attr) {
                    /*  In this case do not look for data
                        type for unsigned/signed.
                        and do use HEX. */
                    chex = TRUE;
                    tdie = NULL;
                }
                /* Do not use hexadecimal format except for
                    DW_AT_ranges. */
                wres = formxdata_print_value(dbg,
                    tdie,attrib,esbp, &err, chex);
                if (wres == DW_DLV_OK) {
                    /* String appended already. */
                } else if (wres == DW_DLV_NO_ENTRY) {
                    /* nothing? */
                } else {
                    print_error(dbg, "Cannot get form data..", wres,
                        err);
                }
                }
                break;
            }
        }
        
        }
        break;
    case DW_FORM_sdata:
        wres = dwarf_formsdata(attrib, &tempsd, &err);
        if (wres == DW_DLV_OK) {
            Dwarf_Bool hxform=TRUE;
            tempud = tempsd;
            formx_unsigned_and_signed_if_neg(tempud,tempsd,
                " (",hxform,esbp);
        } else if (wres == DW_DLV_NO_ENTRY) {
            /* nothing? */
        } else {
            print_error(dbg, "Cannot get formsdata..", wres, err);
        }
        break;
    case DW_FORM_udata:
        wres = dwarf_formudata(attrib, &tempud, &err);
        if (wres == DW_DLV_OK) {
            Dwarf_Bool hex_format = TRUE;
            formx_unsigned(tempud,esbp,hex_format);
        } else if (wres == DW_DLV_NO_ENTRY) {
            /* nothing? */
        } else {
            print_error(dbg, "Cannot get formudata....", wres, err);
        }
        break;
    case DW_FORM_string:
    case DW_FORM_strp:
    case DW_FORM_strx:
    case DW_FORM_strp_sup: /* An offset to alternate file: tied file */
    case DW_FORM_GNU_strp_alt: /* An offset to alternate file: tied file */
    case DW_FORM_GNU_str_index: {
        int sres = dwarf_formstring(attrib, &temps, &err);
        if (sres == DW_DLV_OK) {
            if (theform == DW_FORM_strx ||
                theform == DW_FORM_GNU_str_index) {
                // struct esb_s saver;
                char saver[128];
                Dwarf_Unsigned index = 0;

                // esb_constructor(&saver);
                sres = dwarf_get_debug_str_index(attrib,&index,&err);
                // esb_append(&saver,temps);
                esb_append(saver, temps);

                if(sres == DW_DLV_OK) {
                    bracket_hex("(indexed string: ",index,")",esbp);
                } else {
                    esb_append(esbp,"(indexed string:no string provided?)");
                }
                esb_append(esbp, saver);
                // esb_append(esbp, esb_get_string(&saver));
                // esb_destructor(&saver);
            } else {
                esb_append(esbp,temps);
            }
        } else if (sres == DW_DLV_NO_ENTRY) {
            if (theform == DW_FORM_strx ||
                theform == DW_FORM_GNU_str_index) {
                esb_append(esbp, "(indexed string,no string provided?)");
            } else {
                esb_append(esbp, "<no string provided?>");
            }
        } else {
            if (theform == DW_FORM_strx ||
                theform == DW_FORM_GNU_str_index) {
                print_error(dbg, "Cannot get an indexed string....",
                    sres, err);
            } else {
                print_error(dbg, "Cannot get a formstr (or a formstrp)....",
                    sres, err);
            }
        }
        }
        break;
    case DW_FORM_flag:
        wres = dwarf_formflag(attrib, &tempbool, &err);
        if (wres == DW_DLV_OK) {
            if (tempbool) {
                snprintf(small_buf, sizeof(small_buf), "yes(%d)",
                    tempbool);
                esb_append(esbp, small_buf);
            } else {
                snprintf(small_buf, sizeof(small_buf), "no");
                esb_append(esbp, small_buf);
            }
        } else if (wres == DW_DLV_NO_ENTRY) {
            /* nothing? */
        } else {
            print_error(dbg, "Cannot get formflag/p....", wres, err);
        }
        break;
    case DW_FORM_indirect:
        /*  We should not ever get here, since the true form was
            determined and direct_form has the DW_FORM_indirect if it is
            used here in this attr. */
        esb_append(esbp, get_FORM_name(theform,
            pd_dwarf_names_print_on_error));
        break;
    case DW_FORM_exprloc: {    /* DWARF4 */
        int showhextoo = 1;
        print_exprloc_content(dbg,die,attrib,showhextoo,esbp);
        }
        break;
    case DW_FORM_sec_offset: { /* DWARF4 */
        char* emptyattrname = 0;
        int show_form_here = 0;
        wres = get_small_encoding_integer_and_name(dbg,
            attrib,
            &tempud,
            emptyattrname,
            /* err_string */ NULL,
            (encoding_type_func) 0,
            &err,show_form_here);
        if (wres == DW_DLV_NO_ENTRY) {
            /* Show nothing? */
        } else if (wres == DW_DLV_ERROR) {
            print_error(dbg,
                "Cannot get a  DW_FORM_sec_offset....",
                wres, err);
        } else {
            bracket_hex("",tempud,"",esbp);
        }
        }

        break;
    case DW_FORM_flag_present: /* DWARF4 */
        esb_append(esbp,"yes(1)");
        break;
    case DW_FORM_ref_sig8: {  /* DWARF4 */
        Dwarf_Sig8 sig8data;
        wres = dwarf_formsig8(attrib,&sig8data,&err);
        if (wres != DW_DLV_OK) {
            /* Show nothing? */
            print_error(dbg,
                "Cannot get a  DW_FORM_ref_sig8 ....",
                wres, err);
        } else {
            // struct esb_s sig8str;
            char str_buf[32];
            // esb_constructor(&sig8str);
            // format_sig8_string(&sig8data,&sig8str);
            // esb_append(esbp,esb_get_string(&sig8str));
            // esb_destructor(&sig8str);

            format_sig8_string(&sig8data, str_buf, 32);

            if (!show_form) {
                // esb_append(esbp," <type signature>");
                /* FIXME    */
            }
        }
        }
        break;
    case DW_FORM_GNU_ref_alt: {
        bres = dwarf_global_formref(attrib, &off, &err);
        if (bres == DW_DLV_OK) {
            bracket_hex("",off,"",esbp);
        } else {
            print_error(dbg,
                "DW_FORM_GNU_ref_alt form with no reference?!",
                bres, err);
        }
        }
        break;
    default:
        print_error(dbg, "dwarf_whatform unexpected value", DW_DLV_OK,
            err);
    }
    show_form_itself(show_form,local_verbose,theform, direct_form,esbp);
}

static void
bracket_hex(const char *s1,
    Dwarf_Unsigned v,
    const char *s2,
    char * esbp)
{
    Dwarf_Bool hex_format = TRUE;
    esb_append(esbp,s1);
    // strcat(esbp, s1);
    
    formx_unsigned(v, esbp, hex_format);
    
    esb_append(esbp,s2);
    // strcat(esbp, s2);
}

static void
formx_unsigned(Dwarf_Unsigned u, char *esbp, Dwarf_Bool hex_format)
{
    char small_buf[40];

    if (hex_format) {
        snprintf(small_buf, sizeof(small_buf),"0x%"  DW_PR_XZEROS DW_PR_DUx , u);
    } else {
        snprintf(small_buf, sizeof(small_buf),
            "%" DW_PR_DUu , u);
    }

    esb_append(esbp, small_buf);

    // strcat(esbp, small_buf);
}

static Dwarf_Bool
form_refers_local_info(Dwarf_Half form)
{
    if (form == DW_FORM_GNU_ref_alt ||
        form == DW_FORM_GNU_strp_alt ||
        form == DW_FORM_strp_sup ) {
        /*  These do not refer to the current
            section and cannot be checked
            as if they did. */
        return FALSE;
    }
    return TRUE;
}

static int
formxdata_print_value(Dwarf_Debug dbg,
    Dwarf_Die die,
    Dwarf_Attribute attrib,
    char *esbp,
    Dwarf_Error * pverr, Dwarf_Bool hex_format)
{
    Dwarf_Signed tempsd = 0;
    Dwarf_Unsigned tempud = 0;
    int sres = 0;
    int ures = 0;
    Dwarf_Error serr = 0;

    ures = dwarf_formudata(attrib, &tempud, pverr);
    sres = dwarf_formsdata(attrib, &tempsd, &serr);
    if (ures == DW_DLV_OK) {
        if (sres == DW_DLV_OK) {
            if (tempud == (Dwarf_Unsigned)tempsd && tempsd >= 0) {
                /*  Data is the same value and not negative,
                    so makes no difference which
                    we print. */
                formx_unsigned(tempud,esbp,hex_format);
            } else {
                /*  Here we don't know if signed or not and
                    Assuming one or the other changes the
                    interpretation of the bits. */
                int helpertree_unsigned = 0;

                helpertree_unsigned = check_for_type_unsigned(dbg,die,esbp);
                if (!die || !helpertree_unsigned) {
                    /* Signedness unclear. */
                    formx_unsigned_and_signed_if_neg(tempud,tempsd,
                        " (",hex_format,esbp);
                } else if (helpertree_unsigned > 0) {
                    formx_unsigned(tempud,esbp,hex_format);
                } else {
                    /* Value signed. */
                    formx_signed(tempsd,esbp);
                }
            }
        } else if (sres == DW_DLV_NO_ENTRY) {
            formx_unsigned(tempud,esbp,hex_format);
        } else /* DW_DLV_ERROR */{
            formx_unsigned(tempud,esbp,hex_format);
        }
        goto cleanup;
    } else {
        /* ures ==  DW_DLV_ERROR  or DW_DLV_NO_ENTRY*/
        if (sres == DW_DLV_OK) {
            formx_signed(tempsd,esbp);
        } else {
            /* Neither worked. */
        }
    }
    /*  Clean up any unused Dwarf_Error data.
        DW_DLV_NO_ENTRY cannot really happen,
        so a complete cleanup for that is
        not necessary. */
    cleanup:
    if (sres == DW_DLV_OK || ures == DW_DLV_OK) {
        DROP_ERROR_INSTANCE(dbg,sres,serr);
        DROP_ERROR_INSTANCE(dbg,ures,*pverr);
        return DW_DLV_OK;
    }
    if (sres == DW_DLV_ERROR || ures == DW_DLV_ERROR) {
        if (sres == DW_DLV_ERROR && ures == DW_DLV_ERROR) {
            dwarf_dealloc(dbg,serr,DW_DLA_ERROR);
            serr = 0;
            return DW_DLV_ERROR;
        }
        if (sres == DW_DLV_ERROR) {
            *pverr = serr;
            serr = 0;
        }
        return DW_DLV_ERROR;
    }
    /* Both are DW_DLV_NO_ENTRY which is crazy, impossible. */
    return DW_DLV_NO_ENTRY;
}

static void
formx_unsigned_and_signed_if_neg(Dwarf_Unsigned tempud,
    Dwarf_Signed tempd,
    const char *leader, Dwarf_Bool hex_format, char *esbp)
{
    formx_unsigned(tempud, esbp, hex_format);
    
    if(tempd < 0) {
        esb_append(esbp,leader);
        // strcat(esbp, leader);
        
        formx_signed(tempd,esbp);
        
        esb_append(esbp,")");
        // strcat(esbp, ")");
    }
}

static void
print_exprloc_content(Dwarf_Debug dbg,Dwarf_Die die,
    Dwarf_Attribute attrib,
    int showhextoo, char *esbp)
{
    Dwarf_Ptr x = 0;
    Dwarf_Unsigned tempud = 0;
    char small_buf[80];
    Dwarf_Error ecerr = 0;
    int wres = 0;
    wres = dwarf_formexprloc(attrib,&tempud,&x,&ecerr);
    if (wres == DW_DLV_NO_ENTRY) {
        /* Show nothing?  Impossible. */
    } else if (wres == DW_DLV_ERROR) {
        print_error(dbg, "Cannot get a  DW_FORM_exprloc....", wres, ecerr);
    } else {
        Dwarf_Half address_size = 0;
        Dwarf_Half offset_size = 0;
        Dwarf_Half version = 0;
        int ares = 0;
        unsigned u = 0;
        snprintf(small_buf, sizeof(small_buf),
            "len 0x%04" DW_PR_DUx ": ",tempud);
        esb_append(esbp, small_buf);
        // strcat(esbp, small_buf);
        
        if (showhextoo) {
            for (u = 0; u < tempud; u++) {
                snprintf(small_buf, sizeof(small_buf), "%02x",
                    *(u + (unsigned char *) x));
                esb_append(esbp, small_buf);
                // strcat(esbp, small_buf);
            }
            esb_append(esbp,": ");
            // strcat(esbp,": ");
        }
        ares = dwarf_get_version_of_die(die,&version,&offset_size);
        if (ares != DW_DLV_OK) {
            print_error(dbg,"ERROR: Cannot get version size for exprloc die",
                DW_DLV_ERROR,ecerr);
        }
        ares = dwarf_get_die_address_size(die,&address_size,&ecerr);
        if (wres == DW_DLV_NO_ENTRY) {
            print_error(dbg,"Cannot get die address size for exprloc",
                ares,ecerr);
        } else if (wres == DW_DLV_ERROR) {
            print_error(dbg,"Cannot Get die address size for exprloc",
                ares,ecerr);
        } else {
            get_string_from_locs(dbg,x,tempud,address_size,
                offset_size,version, esbp);
        }
    }
}

static void
show_form_itself(int local_show_form,
    int local_verbose,
    int theform,
    int directform, char *esbp)
{
    char small_buf[100];
    if (local_show_form
        && directform && directform == DW_FORM_indirect) {
        char *form_indir = " (used DW_FORM_indirect";
        char *form_indir2 = ") ";
        esb_append(esbp, form_indir);
        // strcat(esbp, form_indir);
        
        if (local_verbose) {
            esb_append(esbp, get_form_number_as_string(DW_FORM_indirect,
                small_buf,sizeof(small_buf)));
            // strcat(esbp, get_form_number_as_string(DW_FORM_indirect,
            //     small_buf,sizeof(small_buf)));
        }
        
        esb_append(esbp, form_indir2);
        // strcat(esbp, form_indir2);
    }
    if (local_show_form) {
        esb_append(esbp," <form ");
        esb_append(esbp,get_FORM_name(theform,
            pd_dwarf_names_print_on_error));
        
        // strcat(esbp," <form ");
        // strcat(esbp,get_FORM_name(theform,
        //     pd_dwarf_names_print_on_error));

        if (local_verbose) {
            esb_append(esbp, get_form_number_as_string(theform,
                small_buf, sizeof(small_buf)));
            // strcat(esbp, get_form_number_as_string(theform,
            //     small_buf, sizeof(small_buf)));    
        }

        esb_append(esbp,">");
        // strcat(esbp,">");
    }
}

/*  If the DIE DW_AT_type exists and is directly known signed/unsigned
    return -1 for signed 1 for unsigned.
    Otherwise return 0 meaning 'no information'.
    So we only need to a messy lookup once per type-die offset  */
static int
check_for_type_unsigned(Dwarf_Debug dbg,
    Dwarf_Die die,
    char *esbp)
{
    Dwarf_Bool is_info = 0;
    struct Helpertree_Base_s * helperbase = 0;
    struct Helpertree_Map_Entry_s *e = 0;
    int res = 0;
    Dwarf_Attribute attr = 0;
    Dwarf_Attribute encodingattr = 0;
    Dwarf_Error error = 0;
    Dwarf_Unsigned diegoffset = 0;
    Dwarf_Unsigned typedieoffset = 0;
    Dwarf_Die typedie = 0;
    Dwarf_Unsigned tempud = 0;
    int show_form_here = FALSE;
    int retval = 0;

    if(!die) {
        return 0;
    }
    is_info = dwarf_get_die_infotypes_flag(die);
    if(is_info) {
        helperbase = &helpertree_offsets_base_info;
    } else {
        helperbase = &helpertree_offsets_base_types;
    }
    res = dwarf_dieoffset(die,&diegoffset,&error);
    if (res == DW_DLV_ERROR) {
        /* esb_append(esbp,"<helper dieoffset FAIL >"); */
        return 0;
    } else if (res == DW_DLV_NO_ENTRY) {
        /* We don't know sign. */
        /*esb_append(esbp,"<helper dieoffset NO ENTRY>"); */
        return 0;
    }
    /*  This might be wrong. See the typedieoffset check below,
        which is correct... */
    e = helpertree_find(diegoffset,helperbase);
    if(e) {
        /*bracket_hex("<helper FOUND offset ",diegoffset,">",esbp);
        bracket_hex("<helper FOUND val ",e->hm_val,">",esbp); */
        return e->hm_val;
    }

    /*  We look up the DW_AT_type die, if any, and
        use that offset to check for signedness. */

    res = dwarf_attr(die, DW_AT_type, &attr,&error);
    if (res == DW_DLV_ERROR) {
        /*bracket_hex("<helper dwarf_attr FAIL ",diegoffset,">",esbp); */
        helpertree_add_entry(diegoffset, 0,helperbase);
        return 0;
    } else if (res == DW_DLV_NO_ENTRY) {
        /* We don't know sign. */
        /*bracket_hex( "<helper dwarf_attr no entry ",diegoffset,">",esbp); */
        helpertree_add_entry(diegoffset, 0,helperbase);
        return 0;
    }
    res = dwarf_global_formref(attr, &typedieoffset,&error);
    if (res == DW_DLV_ERROR) {
        /*bracket_hex( "<helper global_formreff FAIL" ,diegoffset,">",esbp); */
        dwarf_dealloc(dbg,attr,DW_DLA_ATTR);
        helpertree_add_entry(diegoffset, 0,helperbase);
        return 0;
    } else if (res == DW_DLV_NO_ENTRY) {
        /*esb_append(esbp,"helper NO ENTRY  FAIL ");
        bracket_hex( "<helper global_formreff NO ENTRY" ,diegoffset,">",esbp); */
        dwarf_dealloc(dbg,attr,DW_DLA_ATTR);
        helpertree_add_entry(diegoffset, 0,helperbase);
        return 0;
    }
    dwarf_dealloc(dbg,attr,DW_DLA_ATTR);
    attr = 0;
    e = helpertree_find(typedieoffset,helperbase);
    if(e) {
        /*bracket_hex("<helper FOUND typedieoffset ",typedieoffset,">",esbp);
        bracket_hex("<helper FOUND val ",e->hm_val,">",esbp); */
        return e->hm_val;
    }

    res = dwarf_offdie_b(dbg,typedieoffset,is_info, &typedie,&error);
    if (res == DW_DLV_ERROR) {
        /*bracket_hex( "<helper dwarf_offdie_b  FAIL ",diegoffset,">",esbp); */
        helpertree_add_entry(diegoffset, 0,helperbase);
        helpertree_add_entry(typedieoffset, 0,helperbase);
        return 0;
    } else if (res == DW_DLV_NO_ENTRY) {
        /*bracket_hex( "<helper dwarf_offdie_b  NO ENTRY ",diegoffset,">",esbp); */
        helpertree_add_entry(diegoffset, 0,helperbase);
        helpertree_add_entry(typedieoffset, 0,helperbase);
        return 0;
    }
    res = dwarf_attr(typedie, DW_AT_encoding, &encodingattr,&error);
    if (res == DW_DLV_ERROR) {
        /*bracket_hex( "<helper dwarf_attr typedie  FAIL",diegoffset,">",esbp); */
        dwarf_dealloc(dbg,typedie,DW_DLA_DIE);
        helpertree_add_entry(diegoffset, 0,helperbase);
        helpertree_add_entry(typedieoffset, 0,helperbase);
        return 0;
    } else if (res == DW_DLV_NO_ENTRY) {
        /*bracket_hex( "<helper dwarf_attr typedie  NO ENTRY",diegoffset,">",esbp);*/
        dwarf_dealloc(dbg,typedie,DW_DLA_DIE);
        helpertree_add_entry(diegoffset, 0,helperbase);
        helpertree_add_entry(typedieoffset, 0,helperbase);
        return 0;
    }

    res = get_small_encoding_integer_and_name(dbg,
        encodingattr,
        &tempud,
        /* attrname */ (const char *) NULL,
        /* err_string */ (char *) NULL,
        (encoding_type_func) 0,
        &error,show_form_here);

    if (res != DW_DLV_OK) {
        /*bracket_hex( "<helper small encoding FAIL",diegoffset,">",esbp);*/
        dwarf_dealloc(dbg,typedie,DW_DLA_DIE);
        dwarf_dealloc(dbg,encodingattr,DW_DLA_ATTR);
        helpertree_add_entry(diegoffset, 0,helperbase);
        helpertree_add_entry(typedieoffset, 0,helperbase);
        return 0;
    }
    if (tempud == DW_ATE_signed || tempud == DW_ATE_signed_char) {
        /*esb_append(esbp,"helper small encoding SIGNED ");*/
        retval = -1;
    } else {
        if (tempud == DW_ATE_unsigned || tempud == DW_ATE_unsigned_char) {
            /*esb_append(esbp,"helper small encoding UNSIGNED ");*/
            retval = 1;
        }
    }
    /*bracket_hex( "<helper ENTERED die",diegoffset,">",esbp);
    bracket_hex( "<helper ENTERED typedie",typedieoffset,">",esbp);*/
    helpertree_add_entry(diegoffset,retval,helperbase);
    helpertree_add_entry(typedieoffset, retval,helperbase);
    dwarf_dealloc(dbg,typedie,DW_DLA_DIE);
    dwarf_dealloc(dbg,encodingattr,DW_DLA_ATTR);
    return retval;
}

static char *
get_form_number_as_string(int form, char *buf, unsigned bufsize)
{
    snprintf(buf,bufsize," %d",form);
    return buf;
}

static void
formx_signed(Dwarf_Signed s, char *esbp)
{
    char small_buf[40];

    snprintf(small_buf, sizeof(small_buf),
        "%" DW_PR_DSd ,s);

    esb_append(esbp, small_buf);
    // strcat(esbp, small_buf);
}

void
get_string_from_locs(Dwarf_Debug dbg,
    Dwarf_Ptr bytes_in,
    Dwarf_Unsigned block_len,
    Dwarf_Half addr_size,
    Dwarf_Half offset_size,
    Dwarf_Half version,
    char *out_string)
{
    Dwarf_Locdesc *locdescarray = 0;
    Dwarf_Signed listlen = 0;
    Dwarf_Unsigned ulistlen = 0;
    Dwarf_Error err2 =0;
    int res2 = 0;
    Dwarf_Addr baseaddr = 0; /* Really unknown */

    // if(!glflags.gf_use_old_dwarf_loclist) {
    if (!GLFLAGS_USE_OLD_DWARF_LOCLIST) {
        Dwarf_Loc_Head_c head = 0;
        Dwarf_Locdesc_c locentry = 0;
        int lres = 0;
        Dwarf_Unsigned lopc = 0;
        Dwarf_Unsigned hipc = 0;
        Dwarf_Unsigned ulocentry_count = 0;
        Dwarf_Unsigned section_offset = 0;
        Dwarf_Unsigned locdesc_offset = 0;
        Dwarf_Small lle_value = 0;
        Dwarf_Small loclist_source = 0;

        res2 = dwarf_loclist_from_expr_c(dbg,
            bytes_in,block_len,
            addr_size,
            offset_size,
            version,
            &head,
            &ulistlen,
            &err2);
        if(res2 == DW_DLV_NO_ENTRY) {
            return;
        }
        if(res2 == DW_DLV_ERROR) {
            print_error(dbg, "dwarf_get_loclist_from_expr_c",
                res2, err2);
        }
        lres = dwarf_get_locdesc_entry_c(head,
            0, /* Data from 0th LocDesc */
            &lle_value,
            &lopc, &hipc,
            &ulocentry_count,
            &locentry,
            &loclist_source,
            &section_offset,
            &locdesc_offset,
            &err2);
        if (lres == DW_DLV_ERROR) {
            print_error(dbg, "dwarf_get_locdesc_entry_c", lres, err2);
        } else if (lres == DW_DLV_NO_ENTRY) {
            return;
        }

        dwarfdump_print_one_locdesc(dbg,
            NULL,
            locentry,
            0, /* index 0: locdesc 0 */
            ulocentry_count,
            baseaddr,
            out_string);
        dwarf_loc_head_c_dealloc(head);
        return;
    }
    res2 =dwarf_loclist_from_expr_a(dbg,
        bytes_in,block_len,
        addr_size,
        &locdescarray,
        &listlen,&err2);
    if (res2 == DW_DLV_ERROR) {
        print_error(dbg, "dwarf_get_loclist_from_expr_a",
            res2, err2);
    }
    if (res2==DW_DLV_NO_ENTRY) {
        return;
    }

    /* listlen is always 1 */
    ulistlen = listlen;

    dwarfdump_print_one_locdesc(dbg,
        locdescarray,
        NULL,
        0,
        ulistlen,
        baseaddr,
        out_string);
    dwarf_dealloc(dbg, locdescarray->ld_s, DW_DLA_LOC_BLOCK);
    dwarf_dealloc(dbg, locdescarray, DW_DLA_LOCDESC);
    return ;
}

void
dwarfdump_print_one_locdesc(Dwarf_Debug dbg,
    Dwarf_Locdesc * llbuf, /* Non-zero for old interface. */
    Dwarf_Locdesc_c locdesc,  /* Non-zero for 2015 interface. */
    Dwarf_Unsigned llent, /* Which desc we have . */
    Dwarf_Unsigned entrycount, /* How many location operators (DW_OP)? */
    Dwarf_Addr  baseaddr,
    char *string_out)
{

    Dwarf_Half no_of_ops = 0;
    unsigned i = 0;

    if(llbuf) {
        Dwarf_Locdesc *locd = 0;
        locd = llbuf;
        no_of_ops = llbuf->ld_cents;
        for (i = 0; i < no_of_ops; i++) {
            Dwarf_Loc * op = &locd->ld_s[i];

            int res = _dwarf_print_one_expr_op(dbg,op,NULL,i,
                baseaddr,string_out);
            if (res == DW_DLV_ERROR) {
                return;
            }
        }
        return;
    }
    /* ASSERT: locs != NULL */
    no_of_ops = entrycount;
    for (i = 0; i < no_of_ops; i++) {
        int res = 0;
        res = _dwarf_print_one_expr_op(dbg,NULL,locdesc,i,
            baseaddr,string_out);
        if (res == DW_DLV_ERROR) {
            return;
        }
    }
}

int
_dwarf_print_one_expr_op(Dwarf_Debug dbg,
    Dwarf_Loc* expr,
    Dwarf_Locdesc_c exprc,
    int index,
    Dwarf_Addr baseaddr,
    char *string_out)
{
    /*  local_space_needed is intended to be 'more than big enough'
        for a short group of loclist entries.  */
    char small_buf[100];
    Dwarf_Small op = 0;
    Dwarf_Unsigned opd1 = 0;
    Dwarf_Unsigned opd2 = 0;
    Dwarf_Unsigned opd3 = 0;
    Dwarf_Unsigned offsetforbranch = 0;
    const char * op_name = 0;
    Dwarf_Error onexerr = 0;

    if (index > 0) {
        esb_append(string_out, " ");
    }
    if (expr) {
        /* DWARF 2,3,4 style */
        op = expr->lr_atom;
        opd1 = expr->lr_number;
        opd2 = expr->lr_number2;
    } else {
        /* DWARF 2,3,4 and DWARF5 style */
        int res = dwarf_get_location_op_value_c(exprc,
            index, &op,&opd1,&opd2,&opd3,&offsetforbranch,
            &onexerr);
        if (res != DW_DLV_OK) {
            print_error(dbg,
                "dwarf_get_location_op_value_c unexpected value!",
                DW_DLV_OK, onexerr);
            return DW_DLV_ERROR;
        }
    }
    op_name = get_OP_name(op,pd_dwarf_names_print_on_error);
    esb_append(string_out, op_name);
    if (op_has_no_operands(op)) {
        /* Nothing to add. */
    } else if (op >= DW_OP_breg0 && op <= DW_OP_breg31) {
        snprintf(small_buf, sizeof(small_buf),
            "%+" DW_PR_DSd , (Dwarf_Signed) opd1);
        esb_append(string_out, small_buf);
    } else {
        switch (op) {
        case DW_OP_addr:
            bracket_hex(" ",opd1,"",string_out);
            break;
        case DW_OP_const1s:
        case DW_OP_const2s:
        case DW_OP_const4s:
        case DW_OP_const8s:
        case DW_OP_consts:
        case DW_OP_skip:
        case DW_OP_bra:
        case DW_OP_fbreg:
            esb_append(string_out," ");
            formx_signed(opd1,string_out);
            break;
        case DW_OP_GNU_addr_index: /* unsigned val */
        case DW_OP_addrx: /* DWARF5: unsigned val */
        case DW_OP_GNU_const_index:
        case DW_OP_constx: /* DWARF5: unsigned val */
        case DW_OP_const1u:
        case DW_OP_const2u:
        case DW_OP_const4u:
        case DW_OP_const8u:
        case DW_OP_constu:
        case DW_OP_pick:
        case DW_OP_plus_uconst:
        case DW_OP_regx:
        case DW_OP_piece:
        case DW_OP_deref_size:
        case DW_OP_xderef_size:
            snprintf(small_buf, sizeof(small_buf),
                " %" DW_PR_DUu , opd1);
            esb_append(string_out, small_buf);
            break;
        case DW_OP_bregx:
            bracket_hex(" ",opd1,"",string_out);
            esb_append(string_out,"+");
            formx_signed(opd2,string_out);
            break;
        case DW_OP_call2:
            bracket_hex(" ",opd1,"",string_out);
            break;
        case DW_OP_call4:
            bracket_hex(" ",opd1,"",string_out);
            break;
        case DW_OP_call_ref:
            bracket_hex(" ",opd1,"",string_out);
            break;
        case DW_OP_bit_piece:
            bracket_hex(" ",opd1,"",string_out);
            bracket_hex(" offset ",opd2,"",string_out);
            break;
        case DW_OP_implicit_value:
            {
#define IMPLICIT_VALUE_PRINT_MAX 12
                unsigned int print_len = 0;
                bracket_hex(" ",opd1,"",string_out);
                /*  The other operand is a block of opd1 bytes. */
                /*  FIXME */
                print_len = opd1;
                if (print_len > IMPLICIT_VALUE_PRINT_MAX) {
                    print_len = IMPLICIT_VALUE_PRINT_MAX;
                }
#undef IMPLICIT_VALUE_PRINT_MAX
                {
                    const unsigned char *bp = 0;
                    /*  This is a really ugly cast, a way
                        to implement DW_OP_implicit value in
                        this libdwarf context. */
                    bp = (const unsigned char *) opd2;
                    show_contents(string_out,print_len,bp);
                }
            }
            break;

        /* We do not know what the operands, if any, are. */
        case DW_OP_HP_unknown:
        case DW_OP_HP_is_value:
        case DW_OP_HP_fltconst4:
        case DW_OP_HP_fltconst8:
        case DW_OP_HP_mod_range:
        case DW_OP_HP_unmod_range:
        case DW_OP_HP_tls:
        case DW_OP_INTEL_bit_piece:
            break;
        case DW_OP_stack_value:  /* DWARF4 */
            break;
        case DW_OP_GNU_uninit:  /* DW_OP_APPLE_uninit */
            /* No operands. */
            break;
        case DW_OP_GNU_encoded_addr:
            bracket_hex(" ",opd1,"",string_out);
            break;
        case DW_OP_implicit_pointer:       /* DWARF5 */
        case DW_OP_GNU_implicit_pointer:
            bracket_hex(" ",opd1,"",string_out);
            esb_append(string_out, " ");
            formx_signed(opd2,string_out);
            break;
        case DW_OP_entry_value:       /* DWARF5 */
        case DW_OP_GNU_entry_value: {
            const unsigned char *bp = 0;
            unsigned int length = 0;

            length = opd1;
            bracket_hex(" ",opd1,"",string_out);
            bp = (Dwarf_Small *) opd2;
            if (!bp) {
                esb_append(string_out,
                    "ERROR: Null databyte pointer DW_OP_entry_value ");
            } else {
                show_contents(string_out,length,bp);
            }
            }
            break;
        case DW_OP_const_type:           /* DWARF5 */
        case DW_OP_GNU_const_type:
            {
            const unsigned char *bp = 0;
            unsigned int length = 0;

            bracket_hex(" ",opd1,"",string_out);
            length = opd2;
            esb_append(string_out," const length: ");
            snprintf(small_buf, sizeof(small_buf),
                "%u" , length);
            esb_append(string_out, small_buf);

            /* Now point to the data bytes of the const. */
            bp = (Dwarf_Small *) opd3;
            if (!bp) {
                esb_append(string_out,
                    "ERROR: Null databyte pointer DW_OP_const_type ");
            } else {
                show_contents(string_out,length,bp);
            }
            }
            break;
        case DW_OP_regval_type:           /* DWARF5 */
        case DW_OP_GNU_regval_type: {
            snprintf(small_buf, sizeof(small_buf),
                " 0x%" DW_PR_DUx , opd1);
            esb_append(string_out, small_buf);
            bracket_hex(" ",opd2,"",string_out);
            }
            break;
        case DW_OP_deref_type: /* DWARF5 */
        case DW_OP_GNU_deref_type: {
            snprintf(small_buf, sizeof(small_buf),
                " 0x%02" DW_PR_DUx , opd1);
            esb_append(string_out, small_buf);

            bracket_hex(" ",opd2,"",string_out);
            }
            break;
        case DW_OP_convert: /* DWARF5 */
        case DW_OP_GNU_convert:
        case DW_OP_reinterpret: /* DWARF5 */
        case DW_OP_GNU_reinterpret:
        case DW_OP_GNU_parameter_ref:
            snprintf(small_buf, sizeof(small_buf),
                " 0x%02"  DW_PR_DUx , opd1);
            esb_append(string_out, small_buf);
            break;
        default:
            {
                snprintf(small_buf, sizeof(small_buf),
                    " dwarf_op unknown 0x%x", (unsigned)op);
                esb_append(string_out,small_buf);
            }
            break;
        }
    }
    return DW_DLV_OK;
}


static int
op_has_no_operands(int op)
{
    unsigned i = 0;
    if (op >= DW_OP_lit0 && op <= DW_OP_reg31) {
        return TRUE;
    }
    for (; ; ++i) {
        struct operation_descr_s *odp = opdesc+i;
        if (odp->op_code == 0) {
            break;
        }
        if (odp->op_code != op) {
            continue;
        }
        if (odp->op_count == 0) {
            return TRUE;
        }
        return FALSE;
    }
    return FALSE;
}

static void
show_contents(char *string_out,
    unsigned int length,const unsigned char * bp)
{
    unsigned int i = 0;
    char small_buf[20];

    if(!length) {
        return;
    }

    esb_append(string_out," contents 0x");
    // strcat(string_out," contents 0x");
    
    for (; i < length; ++i,++bp) {
        /*  Do not use DW_PR_DUx here,
            the value  *bp is a const unsigned char. */
        snprintf(small_buf, sizeof(small_buf),
            "%02x", *bp);

        esb_append(string_out,small_buf);
        // strcat(string_out,small_buf);
    }
}

