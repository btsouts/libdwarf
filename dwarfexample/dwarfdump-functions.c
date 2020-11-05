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

#ifdef _MSC_VER
#include <stdint.h>
#include <io.h>
#endif

#include <ctype.h>

enum line_flag_type_e {
  singledw5,   /* Meaning choose single table DWARF5 new interfaces. */
  s2l,   /* Meaning choose two-level DWARF5 new interfaces. */
  orig,  /* Meaning choose DWARF2,3,4 single level interface. */
  orig2l /* Meaning choose DWARF 2,3,4 two-level interface. */
};

// #include "tracing-types.h"
// #include "dwarfdump-functions.h"
#include "dwarf-parsing.h"

#include "../dwarfdump/naming.h"
#include "../dwarfdump/helpertree.h"
#include "../dwarfdump/checkutil.h"
#include "../dwarfdump/addrmap.h"
#include "../dwarfdump/glflags.h"

/* Used to try to avoid leakage when we hide errors. */
#define DROP_ERROR_INSTANCE(d,r,e)       \
    if (r == DW_DLV_ERROR) {             \
        dwarf_dealloc(d,e,DW_DLA_ERROR); \
        e = 0;                           \
    }

static int pd_dwarf_names_print_on_error = 1;

static void print_die_data(Dwarf_Debug dbg, Dwarf_Die print_me,
    int level,
    struct srcfilesdata *sf);

static void get_die_and_siblings(Dwarf_Debug dbg, Dwarf_Die in_die,
    int is_info, int in_level,
    struct srcfilesdata *sf);

static void resetsrcfiles(Dwarf_Debug dbg,struct srcfilesdata *sf);

static void
print_error_maybe_continue(Dwarf_Debug dbg,
    const char * msg,
    int dwarf_code,
    Dwarf_Error lerr,
    Dwarf_Bool do_continue);

static void
bracket_hex(const char *s1,
    Dwarf_Unsigned v,
    const char *s2,
    char * esbp);

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

void
get_address_size_and_max(Dwarf_Debug dbg,
   Dwarf_Half * size,
   Dwarf_Addr * max,
   Dwarf_Error *aerr);

int
get_proc_name(Dwarf_Debug dbg, Dwarf_Die die, Dwarf_Addr low_pc,
    char *proc_name_buf, int proc_name_buf_len, void **pcMap);

void PRINT_CU_INFO(void);

boolean
checking_this_compiler(void);

static const char *
adexplain(Dwarf_Unsigned liberr,
   const char * alterr);

static void
loc_error_check(Dwarf_Debug dbg,
    Dwarf_Addr lopcfinal,
    Dwarf_Addr lopc,
    Dwarf_Addr hipcfinal,
    Dwarf_Addr hipc,
    Dwarf_Unsigned offset,
    Dwarf_Addr base_address,
    Dwarf_Bool *bError);

void
print_error_and_continue(Dwarf_Debug dbg,
    const char * msg,
    int dwarf_code,
    Dwarf_Error lerr);

void
record_range_array_info_entry(Dwarf_Off die_off,Dwarf_Off range_off);

void
print_ranges_list_to_extra(Dwarf_Debug dbg,
    Dwarf_Unsigned off,
    Dwarf_Ranges *rangeset,
    Dwarf_Signed rangecount,
    Dwarf_Unsigned bytecount,
    char *stringbuf);

static const char *
get_rangelist_type_descr(Dwarf_Ranges *r);

boolean
is_strstrnocase(const char * container, const char * contained);

static int
get_abstract_origin_funcname(Dwarf_Debug dbg, Dwarf_Attribute attr,
    char *name_out, unsigned maxlen);

static boolean
cu_data_is_set(void);    

static void
load_CU_error_data(Dwarf_Debug dbg, Dwarf_Die cu_die);

void
safe_strcpy(char *out, long outlen, const char *in, long inlen);

void
print_line_numbers_this_cu(Dwarf_Debug dbg, Dwarf_Die cu_die);

static void
print_source_intro(Dwarf_Debug dbg,Dwarf_Die cu_die);

static void
print_line_context_record(Dwarf_Debug dbg,
    Dwarf_Line_Context line_context);

static void
process_line_table(Dwarf_Debug dbg,
    const char *sec_name,
    Dwarf_Line *linebuf, Dwarf_Signed linecount,
    Dwarf_Bool is_logicals_table, Dwarf_Bool is_actuals_table);

static void
record_line_error(const char *where, Dwarf_Error line_err);

void
translate_to_uri(const char * filename, char *out);

#if 0
DW_UT_compile                   0x01  /* DWARF5 */
DW_UT_type                      0x02  /* DWARF5 */
DW_UT_partial                   0x03  /* DWARF5 */
#endif

boolean show_form_used = FALSE;

int verbose = 0;

/*  Base address has a special meaning in DWARF4 relative to address ranges. */
boolean seen_PU = FALSE;              /* Detected a PU */
boolean seen_CU = FALSE;              /* Detected a CU */
boolean need_CU_name = TRUE;          /* Need CU name */
boolean need_CU_base_address = TRUE;  /* Need CU Base address */
boolean need_CU_high_address = TRUE;  /* Need CU High address */
boolean need_PU_valid_code = TRUE;    /* Need PU valid code */

boolean seen_PU_base_address = FALSE; /* Detected a Base address for PU */
boolean seen_PU_high_address = FALSE; /* Detected a High address for PU */
Dwarf_Addr PU_base_address = 0;       /* PU Base address */
Dwarf_Addr PU_high_address = 0;       /* PU High address */

Dwarf_Off  DIE_offset = 0;            /* DIE offset in compile unit */
Dwarf_Off  DIE_overall_offset = 0;    /* DIE offset in .debug_info */

/*  These globals  enable better error reporting. */
Dwarf_Off  DIE_CU_offset = 0;         /* CU DIE offset in compile unit */
Dwarf_Off  DIE_CU_overall_offset = 0; /* CU DIE offset in .debug_info */
int current_section_id = 0;           /* Section being process */

/*  Base Address is needed for range lists and must come from a CU.
    Low address is for information and can come from a function
    or something in the CU. */
Dwarf_Addr CU_base_address = 0;       /* CU Base address */
Dwarf_Addr CU_low_address = 0;        /* CU low address */
Dwarf_Addr CU_high_address = 0;       /* CU High address */

const char *search_any_text = 0;
const char *search_match_text = 0;
const char *search_regex_text = 0;
int search_occurrences = 0;

#ifdef HAVE_REGEX
/* -S option: the compiled_regex */
regex_t search_re;
#endif

/* The following too is related to high and low pc
attributes of a function. It's misnamed, it really means
'yes, we have high and low pc' if it is TRUE. Defaulting to TRUE
seems bogus. */
static Dwarf_Bool in_valid_code = TRUE;

/* Check categories corresponding to the -k option */
typedef enum /* Dwarf_Check_Categories */ {
    abbrev_code_result,
    pubname_attr_result,
    reloc_offset_result,
    attr_tag_result,
    tag_tree_result,
    type_offset_result,
    decl_file_result,
    ranges_result,
    lines_result,
    aranges_result,
    /*  Harmless errors are errors detected inside libdwarf but
        not reported via DW_DLE_ERROR returns because the errors
        won't really affect client code.  The 'harmless' errors
        are reported and otherwise ignored.  It is difficult to report
        the error when the error is noticed by libdwarf, the error
        is reported at a later time.
        The other errors dwarfdump reports are also generally harmless
        but are detected by dwarfdump so it's possble to report the
        error as soon as the error is discovered. */
    harmless_result,
    fde_duplication,
    frames_result,
    locations_result,
    names_result,
    abbreviations_result,
    dwarf_constants_result,
    di_gaps_result,
    forward_decl_result,
    self_references_result,
    attr_encoding_result,
    duplicated_attributes_result,
    total_check_result,
    LAST_CATEGORY  /* Must be last */
} Dwarf_Check_Categories;

/* pRangesInfo records the DW_AT_high_pc and DW_AT_low_pc
   and is used to check that line range info falls inside
   the known valid ranges.   The data is per CU, and is
   reset per CU in tag_specific_checks_setup(). */
Bucket_Group *pRangesInfo = NULL;

/* These names make diagnostic messages more complete, the
   fixed length is safe, though ultra long names will get
   truncated. */
#define COMPILE_UNIT_NAME_LEN 512

char PU_name[COMPILE_UNIT_NAME_LEN];
char CU_name[COMPILE_UNIT_NAME_LEN];
char CU_producer[COMPILE_UNIT_NAME_LEN];

Bucket_Group *pVisitedInfo = NULL;

boolean dump_visited_info = FALSE;

boolean dense = FALSE;

/* Is this a PU has been invalidated by the SN Systems linker? */
#define IsInvalidCode(low,high) ((low == elf_max_address) || (low == 0 && high == 0))

/* Section IDs */
#define DEBUG_ABBREV      1
#define DEBUG_ARANGES     2
#define DEBUG_FRAME       3
#define DEBUG_INFO        4
#define DEBUG_LINE        5
#define DEBUG_LOC         6
#define DEBUG_MACINFO     7
#define DEBUG_PUBNAMES    8
#define DEBUG_RANGES      9
#define DEBUG_STATIC_VARS 10
#define DEBUG_STATIC_FUNC 11
#define DEBUG_STR         12
#define DEBUG_WEAKNAMES   13
#define DEBUG_TYPES       14
#define DEBUG_GDB_INDEX   15
#define DEBUG_FRAME_EH_GNU 16
#define DEBUG_MACRO       17
#define DEBUG_NAMES       18

/* pLinkonceInfo records data about the link once sections.
   If a line range is not valid in the current CU it might
   be valid in a linkonce section, this data records the
   linkonce sections.  So it is filled in when an
   object file is read and remains unchanged for an entire
   object file.  */
Bucket_Group *pLinkonceInfo = NULL;

/*  Records information about compilers (producers) found in the
    debug information, including the check results for several
    categories (see -k option). */
typedef struct {
    Dwarf_Off die_off;
    Dwarf_Off range_off;
} Range_Array_Entry;

/*  Array to record the DW_AT_range attribute DIE, to be used at the end
    of the CU, to check the range values; DWARF4 allows an offset relative
    to the low_pc as the high_pc value. Also, LLVM generates for the CU the
    pair (low_pc, at_ranges) instead of the traditional (low_pc, high_pc).
*/
static Range_Array_Entry *range_array = NULL;
static Dwarf_Unsigned range_array_size = 0;
static Dwarf_Unsigned range_array_count = 0;
#define RANGE_ARRAY_INITIAL_SIZE 64

/*  Making this a named string makes it simpler to change
    what the reset,or 'I do not know'  value is for
    CU name or producer name for PRINT_CU_INFO. */
static const char * default_cu_producer = "<unknown>";

struct die_stack_data_s {
    Dwarf_Die die_;
    /*  sibling_die_globaloffset_ is set while processing the DIE.
        We do not know the sibling global offset
        when we create the stack entry.
        If the sibling attribute absent we never know. */
    Dwarf_Off sibling_die_globaloffset_;
    /*  We may need is_info here too. */
    Dwarf_Off cu_die_offset_; /* global offset. */
    boolean already_printed_;
};
struct die_stack_data_s empty_stack_entry;

Dwarf_Die current_cu_die_for_print_frames;

struct glflags_s glflags;

/*  The type of Bucket. */
#define KIND_RANGES_INFO       1
#define KIND_SECTIONS_INFO     2
#define KIND_VISITED_INFO      3

boolean ellipsis = FALSE;

/* dwarfdump_ctype table. See uritablebuild.c */
static char dwarfdump_ctype_table[256] = {
0, /* NUL 0x00 */
0, /* control 0x01 */
0, /* control 0x02 */
0, /* control 0x03 */
0, /* control 0x04 */
0, /* control 0x05 */
0, /* control 0x06 */
0, /* control 0x07 */
0, /* control 0x08 */
0, /* whitespace 0x09 */
0, /* whitespace 0x0a */
0, /* whitespace 0x0b */
0, /* whitespace 0x0c */
0, /* whitespace 0x0d */
0, /* control 0x0e */
0, /* control 0x0f */
0, /* control 0x10 */
0, /* control 0x11 */
0, /* control 0x12 */
0, /* control 0x13 */
0, /* control 0x14 */
0, /* control 0x15 */
0, /* control 0x16 */
0, /* control 0x17 */
0, /* control 0x18 */
0, /* control 0x19 */
0, /* control 0x1a */
0, /* control 0x1b */
0, /* control 0x1c */
0, /* control 0x1d */
0, /* control 0x1e */
0, /* control 0x1f */
1, /* ' ' 0x20 */
1, /* '!' 0x21 */
0, /* '"' 0x22 */
1, /* '#' 0x23 */
1, /* '$' 0x24 */
0, /* '%' 0x25 */
1, /* '&' 0x26 */
0, /* ''' 0x27 */
1, /* '(' 0x28 */
1, /* ')' 0x29 */
1, /* '*' 0x2a */
1, /* '+' 0x2b */
1, /* ',' 0x2c */
1, /* '-' 0x2d */
1, /* '.' 0x2e */
1, /* '/' 0x2f */
1, /* '0' 0x30 */
1, /* '1' 0x31 */
1, /* '2' 0x32 */
1, /* '3' 0x33 */
1, /* '4' 0x34 */
1, /* '5' 0x35 */
1, /* '6' 0x36 */
1, /* '7' 0x37 */
1, /* '8' 0x38 */
1, /* '9' 0x39 */
1, /* ':' 0x3a */
0, /* ';' 0x3b */
1, /* '<' 0x3c */
1, /* '=' 0x3d */
1, /* '>' 0x3e */
1, /* '?' 0x3f */
1, /* '@' 0x40 */
1, /* 'A' 0x41 */
1, /* 'B' 0x42 */
1, /* 'C' 0x43 */
1, /* 'D' 0x44 */
1, /* 'E' 0x45 */
1, /* 'F' 0x46 */
1, /* 'G' 0x47 */
1, /* 'H' 0x48 */
1, /* 'I' 0x49 */
1, /* 'J' 0x4a */
1, /* 'K' 0x4b */
1, /* 'L' 0x4c */
1, /* 'M' 0x4d */
1, /* 'N' 0x4e */
1, /* 'O' 0x4f */
1, /* 'P' 0x50 */
1, /* 'Q' 0x51 */
1, /* 'R' 0x52 */
1, /* 'S' 0x53 */
1, /* 'T' 0x54 */
1, /* 'U' 0x55 */
1, /* 'V' 0x56 */
1, /* 'W' 0x57 */
1, /* 'X' 0x58 */
1, /* 'Y' 0x59 */
1, /* 'Z' 0x5a */
1, /* '[' 0x5b */
1, /* '\' 0x5c */
1, /* ']' 0x5d */
1, /* '^' 0x5e */
1, /* '_' 0x5f */
0, /* '`' 0x60 */
1, /* 'a' 0x61 */
1, /* 'b' 0x62 */
1, /* 'c' 0x63 */
1, /* 'd' 0x64 */
1, /* 'e' 0x65 */
1, /* 'f' 0x66 */
1, /* 'g' 0x67 */
1, /* 'h' 0x68 */
1, /* 'i' 0x69 */
1, /* 'j' 0x6a */
1, /* 'k' 0x6b */
1, /* 'l' 0x6c */
1, /* 'm' 0x6d */
1, /* 'n' 0x6e */
1, /* 'o' 0x6f */
1, /* 'p' 0x70 */
1, /* 'q' 0x71 */
1, /* 'r' 0x72 */
1, /* 's' 0x73 */
1, /* 't' 0x74 */
1, /* 'u' 0x75 */
1, /* 'v' 0x76 */
1, /* 'w' 0x77 */
1, /* 'x' 0x78 */
1, /* 'y' 0x79 */
1, /* 'z' 0x7a */
1, /* '{' 0x7b */
1, /* '|' 0x7c */
1, /* '}' 0x7d */
1, /* '~' 0x7e */
0, /* DEL 0x7f */
1, /* 0x80 */
1, /* 0x81 */
1, /* 0x82 */
1, /* 0x83 */
1, /* 0x84 */
1, /* 0x85 */
1, /* 0x86 */
1, /* 0x87 */
1, /* 0x88 */
1, /* 0x89 */
1, /* 0x8a */
1, /* 0x8b */
1, /* 0x8c */
1, /* 0x8d */
1, /* 0x8e */
1, /* 0x8f */
1, /* 0x90 */
1, /* 0x91 */
1, /* 0x92 */
1, /* 0x93 */
1, /* 0x94 */
1, /* 0x95 */
1, /* 0x96 */
1, /* 0x97 */
1, /* 0x98 */
1, /* 0x99 */
1, /* 0x9a */
1, /* 0x9b */
1, /* 0x9c */
1, /* 0x9d */
1, /* 0x9e */
1, /* 0x9f */
0, /* other: 0xa0 */
1, /* 0xa1 */
1, /* 0xa2 */
1, /* 0xa3 */
1, /* 0xa4 */
1, /* 0xa5 */
1, /* 0xa6 */
1, /* 0xa7 */
1, /* 0xa8 */
1, /* 0xa9 */
1, /* 0xaa */
1, /* 0xab */
1, /* 0xac */
1, /* 0xad */
1, /* 0xae */
1, /* 0xaf */
1, /* 0xb0 */
1, /* 0xb1 */
1, /* 0xb2 */
1, /* 0xb3 */
1, /* 0xb4 */
1, /* 0xb5 */
1, /* 0xb6 */
1, /* 0xb7 */
1, /* 0xb8 */
1, /* 0xb9 */
1, /* 0xba */
1, /* 0xbb */
1, /* 0xbc */
1, /* 0xbd */
1, /* 0xbe */
1, /* 0xbf */
1, /* 0xc0 */
1, /* 0xc1 */
1, /* 0xc2 */
1, /* 0xc3 */
1, /* 0xc4 */
1, /* 0xc5 */
1, /* 0xc6 */
1, /* 0xc7 */
1, /* 0xc8 */
1, /* 0xc9 */
1, /* 0xca */
1, /* 0xcb */
1, /* 0xcc */
1, /* 0xcd */
1, /* 0xce */
1, /* 0xcf */
1, /* 0xd0 */
1, /* 0xd1 */
1, /* 0xd2 */
1, /* 0xd3 */
1, /* 0xd4 */
1, /* 0xd5 */
1, /* 0xd6 */
1, /* 0xd7 */
1, /* 0xd8 */
1, /* 0xd9 */
1, /* 0xda */
1, /* 0xdb */
1, /* 0xdc */
1, /* 0xdd */
1, /* 0xde */
1, /* 0xdf */
1, /* 0xe0 */
1, /* 0xe1 */
1, /* 0xe2 */
1, /* 0xe3 */
1, /* 0xe4 */
1, /* 0xe5 */
1, /* 0xe6 */
1, /* 0xe7 */
1, /* 0xe8 */
1, /* 0xe9 */
1, /* 0xea */
1, /* 0xeb */
1, /* 0xec */
1, /* 0xed */
1, /* 0xee */
1, /* 0xef */
1, /* 0xf0 */
1, /* 0xf1 */
1, /* 0xf2 */
1, /* 0xf3 */
1, /* 0xf4 */
1, /* 0xf5 */
1, /* 0xf6 */
1, /* 0xf7 */
1, /* 0xf8 */
1, /* 0xf9 */
1, /* 0xfa */
1, /* 0xfb */
1, /* 0xfc */
1, /* 0xfd */
1, /* 0xfe */
0, /* other: 0xff */
};

static char *
xchar(int c, char *buf, int size)
{
    snprintf(buf, size,"%%%02x",c);
    return buf;
}

/*  When we add a 'print' option after an option
    requests one or more checks
    we turn off all checking, putting it back to default
    checking state. */
static void
set_checks_off()
{
    glflags.gf_check_abbrev_code = FALSE;
    glflags.gf_check_pubname_attr = FALSE;
    glflags.gf_check_reloc_offset = FALSE;
    glflags.gf_check_attr_tag = FALSE;
    glflags.gf_check_tag_tree = FALSE;
    glflags.gf_check_type_offset = FALSE;
    glflags.gf_check_decl_file = FALSE;
    glflags.gf_check_lines = FALSE;
    glflags.gf_check_fdes = FALSE;
    glflags.gf_check_ranges = FALSE;
    glflags.gf_check_aranges = FALSE;
    glflags.gf_check_harmless = FALSE;
    glflags.gf_check_abbreviations = FALSE;
    glflags.gf_check_dwarf_constants = FALSE;
    glflags.gf_check_di_gaps = FALSE;
    glflags.gf_check_forward_decl = FALSE;
    glflags.gf_check_self_references = FALSE;
    glflags.gf_check_attr_encoding = FALSE;
    glflags.gf_check_duplicated_attributes = FALSE;
    glflags.gf_check_debug_names = FALSE;
}

static void suppress_check_dwarf()
{
    glflags.gf_do_print_dwarf = TRUE;
    if (glflags.gf_do_check_dwarf) {
        printf("Warning: check flag turned off, "
            "checking and printing are separate.\n");
    }
    glflags.gf_do_check_dwarf = FALSE;
    set_checks_off();
}

/* ----------------------- */

static int unittype      = DW_UT_compile;

int cu_version_stamp = 0;
int cu_offset_size = 0;

/*  dienumberr is used to count DIEs.
    The point is to match fissionfordie. */
static int dienumber = 0;
static int fissionfordie = -1;
static int passnullerror = 0;
/*  These hash representations have to be converted to Dwarf_Sig8
    before use. */

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
esb_empty_string(char *inputStr)
{
    if (inputStr != NULL)
    {
        // strcpy(inputStr, "");
        inputStr[0] = '\0';
    }
    else
    {
        fprintf(stderr, "esb_empty_string: inputStr is NULL.\n");
    }
    
}

static char *
esb_get_string(char *inputStr)
{
    if (inputStr != NULL)
    {
        
    }
    else
    {
        fprintf(stderr, "esb_get_string: inputStr is NULL.\n");
    }
    
    return inputStr;
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

void
intGlFlags(void)
{
    glflags.gf_check_attr_tag = 1;
    glflags.gf_print_usage_tag_attr = 1;
    glflags.gf_check_ranges = 1;
    glflags.gf_check_decl_file = 1;
    glflags.gf_check_locations = 1;
    glflags.gf_check_verbose_mode = 1;
    glflags.gf_check_names = 1;
    glflags.gf_do_check_dwarf = 1;
    glflags.gf_search_is_on = 1;
    glflags.gf_check_forward_decl = 1;
    glflags.gf_check_self_references = 1;
    glflags.gf_search_wide_format = 1;
    glflags.gf_display_offsets = 1;
    glflags.gf_show_global_offsets = 1;
    glflags.gf_check_type_offset = 1;
    glflags.gf_use_old_dwarf_loclist = 0;
    glflags.gf_suppress_checking_on_dwp = 1;
    glflags.gf_do_print_dwarf = 1;

    glflags.gf_info_flag = TRUE;
    glflags.gf_types_flag = TRUE;
    suppress_check_dwarf();
}

void
read_cu_list(Dwarf_Debug dbg, Dwarf_Bool is_info)
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
    // Dwarf_Bool     is_info = g_is_info;
    Dwarf_Error error;
    int cu_number = 0;
    Dwarf_Error *errp  = 0;


    for(;;++cu_number) {
    // for(;cu_number<3;cu_number++) {    
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
        res = dwarf_siblingof_b(dbg, no_die, is_info,
            &cu_die, errp);

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

        Dwarf_Off DIE_CU_header_overall_offset;

        /*  To erase    */ 
        // char *name = 0;
        // Dwarf_Off header_overall_offset = 0;
        // Dwarf_Off overall_offset = 0;
        // Dwarf_Off offset = 0;

        // res = dwarf_diename(cu_die, &name, errp);

        // res = dwarf_dieoffset(cu_die, &overall_offset, errp);

        // res = dwarf_die_CU_offset(cu_die, &offset, errp);

        // header_overall_offset = overall_offset - offset;

        /*  See print_cu_hdr_cudie  */
        // printf("CU number: %d CU name: %s, Header overall offset: 0x%llX\n",  cu_number, name, header_overall_offset);

            Dwarf_Error pod_err;
            Dwarf_Error srcerr = 0;
            // Dwarf_Off dieprint_cu_goffset = 0;

            int srcf = dwarf_srcfiles(cu_die,
                &sf.srcfiles, &sf.srcfilescount, &srcerr);
            if (srcf == DW_DLV_ERROR) {
                print_error_and_continue(dbg, "dwarf_srcfiles",
                    srcf,srcerr);
                dwarf_dealloc(dbg,srcerr,DW_DLA_ERROR);
                srcerr = 0;
                sf.srcfiles = NULL;
                sf.srcfilescount = 0;
            } /*DW_DLV_NO_ENTRY generally means there
                there is no dW_AT_stmt_list attribute.
                and we do not want to print anything
                about statements in that case */

            /* Get the CU offset for easy error reporting */
            dwarf_die_offsets(cu_die,&DIE_overall_offset,&DIE_offset,&pod_err);
            DIE_CU_overall_offset = DIE_overall_offset;
            DIE_CU_offset = DIE_offset;
            DIE_CU_header_overall_offset = DIE_CU_overall_offset - DIE_CU_offset;

            // printf("CU number: %d CU name: %s, DIE_CU_overall_offset - DIE_CU_offset: 0x%llX\n",  cu_number, name, (DIE_CU_overall_offset - DIE_CU_offset));

        if (cuAllowedForParsing(DIE_CU_header_overall_offset))
        {    
            get_die_and_siblings(dbg,cu_die,is_info,0,&sf);

            /*  Traverse the line section if in check mode
                or if line-printing requested */
            if (glflags.gf_line_flag || glflags.gf_check_decl_file) {
                int oldsection = current_section_id;
                print_line_numbers_this_cu(dbg, cu_die);
                current_section_id = oldsection;
            }
        }

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
    // Dwarf_Half formnum = 0;
    // const char *formname = 0;
    
    Dwarf_Signed i = 0;
    Dwarf_Signed atcnt = 0;
    Dwarf_Attribute *atlist = 0;
    int atres = 0;
    Dwarf_Error podie_err = 0;

    Dwarf_Off  DIE_offset = 0;            /* DIE offset in compile unit */
    Dwarf_Off  DIE_overall_offset = 0;    /* DIE offset in .debug_info */

    Dwarf_Off dieprint_cu_goffset = 0;

    Dwarf_Off offset = 0;
    Dwarf_Off overall_offset = 0;
    int ores = 0;

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
    
    ores = dwarf_dieoffset(print_me, &overall_offset, &podie_err);
    if (ores != DW_DLV_OK) {
        print_error(dbg, "dwarf_dieoffset", ores, podie_err);
    }
    ores = dwarf_die_CU_offset(print_me, &offset, &podie_err);
    if (ores != DW_DLV_OK) {
        print_error(dbg, "dwarf_die_CU_offset", ores, podie_err);
    }

#ifdef PRINT_DEBUG_MESSAGES
    if (glflags.gf_show_global_offsets) {
        printf("<%2d><0x%" DW_PR_XZEROS DW_PR_DUx
            " GOFF=0x%" DW_PR_XZEROS DW_PR_DUx ">",
            level, (Dwarf_Unsigned)offset,
            (Dwarf_Unsigned)overall_offset);
    } else {
        printf("<%2d><0x%" DW_PR_XZEROS DW_PR_DUx ">",
            level,
            (Dwarf_Unsigned)offset);
    }

    /* Print using indentation */
    /*  This is where top level constructs are printed  */
    printf("%*s%s",level * 2 + 2," ",tagname);
    printf("\n");
#endif

    atres = dwarf_attrlist(print_me, &atlist, &atcnt, &podie_err);

    if (atres == DW_DLV_ERROR) {
        print_error(dbg, "dwarf_attrlist", atres, podie_err);
    } else if (atres == DW_DLV_NO_ENTRY) {
        /* indicates there are no attrs.  It is not an error. */
        atcnt = 0;
    }

    /* Get the offset for easy error reporting: This is not the CU die.  */
    dwarf_die_offsets(print_me, &DIE_overall_offset, &DIE_offset, &podie_err);

    parseCompilationUnit(dbg, print_me, overall_offset,
        tag, atlist, atcnt, dieprint_cu_goffset, level, sf); 
    
    for (i = 0; i < atcnt; i++) {
        dwarf_dealloc(dbg, atlist[i], DW_DLA_ATTR);
    }

    if (atres == DW_DLV_OK) {
        dwarf_dealloc(dbg, atlist, DW_DLA_LIST);
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

void
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

int
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
    char buf[100];              /* The strings are small. */

    // printf("get_small_encoding_integer_and_name: Entering\n");

    int vres = dwarf_formudata(attrib, &uval, seierr);

    if (vres != DW_DLV_OK) {
        Dwarf_Signed sval = 0;
        if(vres == DW_DLV_ERROR) {
            dwarf_dealloc(dbg,*seierr, DW_DLV_ERROR);
            *seierr = 0;
        }
        vres = dwarf_formsdata(attrib, &sval, seierr);
        if (vres != DW_DLV_OK) {
            vres = dwarf_global_formref(attrib,&uval,seierr);
            if (vres != DW_DLV_OK) {
                if (string_out != 0) {
                    snprintf(buf, sizeof(buf),
                        "%s has a bad form.", attr_name);
                    esb_append(string_out,buf);
                }
                return vres;
            }
            *uval_out = uval;
        } else {
            uval =  (Dwarf_Unsigned) sval;
            *uval_out = uval;
        }
    } else {
        *uval_out = uval;
    }

    if (string_out) {
        Dwarf_Half theform = 0;
        Dwarf_Half directform = 0;
        // struct esb_s fstring;
        char fstring[ESB_S_CHAR_LENGTH];

        esb_constructor(fstring);
        get_form_values(dbg,attrib,&theform,&directform);
        esb_append(fstring, val_as_string((Dwarf_Half) uval,
            pd_dwarf_names_print_on_error));
        show_form_itself(show_form, verbose, theform, directform, fstring);
        esb_append(string_out, esb_get_string(fstring));
        // esb_destructor(&fstring);
    }

    return DW_DLV_OK;   
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
    Dwarf_Bool tempbool = 0;
    Dwarf_Addr addr = 0;
    int fres = 0;
    int bres = 0;
    int wres = 0;
    int dres = 0;
    Dwarf_Half direct_form = 0;
    char small_buf[512];  /* Size to hold a filename COMPILE_UNIT_NAME_LEN */
    Dwarf_Error err = 0;

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

    // printf("Examing theform: 0x%X\n", theform);

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
        if (glflags.gf_show_global_offsets) {
            bracket_hex("<",off,"",esbp);
            bracket_hex(" GOFF=",goff,">",esbp);
        } else {
            bracket_hex("<",off,">",esbp);
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
            {    
                int show_form_here = 0;
                wres = get_small_encoding_integer_and_name(dbg,
                    attrib,
                    &tempud,
                    /* attrname */ (const char *) NULL,
                    /* err_string */ ( char *) NULL,
                    (encoding_type_func) 0,
                    &err,show_form_here);

                if (wres == DW_DLV_OK) {
                    Dwarf_Bool hex_format = TRUE;
                    formx_unsigned(tempud,esbp,hex_format);
                    /* Check attribute encoding */
                    if (glflags.gf_check_attr_encoding) {
                        // check_attributes_encoding(attr,theform,tempud);
                    }

                    if (attr == DW_AT_decl_file || attr == DW_AT_call_file) {
                        if (srcfiles && tempud > 0 &&
                            /* ASSERT: cnt >= 0 */
                            tempud <= (Dwarf_Unsigned)cnt) {
                            /*  added by user request */
                            /*  srcfiles is indexed starting at 0, but
                                DW_AT_decl_file defines that 0 means no
                                file, so tempud 1 means the 0th entry in
                                srcfiles, thus tempud-1 is the correct
                                index into srcfiles.  */
                            char *fname = srcfiles[tempud - 1];

                            esb_append(esbp, " ");
                            esb_append(esbp, fname);
                        }
                    }
                } else {
                    print_error(dbg, "Cannot get encoding attribute ..",
                        wres, err);
                }
            }
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

                esb_constructor(saver);
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
            // esb_constructor(sig8str);
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

void
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

void
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

void
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

    if(!glflags.gf_use_old_dwarf_loclist) {
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

/*  Does not return on error. */
void
get_address_size_and_max(Dwarf_Debug dbg,
   Dwarf_Half * size,
   Dwarf_Addr * max,
   Dwarf_Error *aerr)
{
    int dres = 0;
    Dwarf_Half lsize = 4;
    /* Get address size and largest representable address */
    dres = dwarf_get_address_size(dbg,&lsize,aerr);
    if (dres != DW_DLV_OK) {
        print_error(dbg, "get_address_size()", dres, *aerr);
    }
    if(max) {
        *max = (lsize == 8 ) ? 0xffffffffffffffffULL : 0xffffffff;
    }
    if(size) {
        *size = lsize;
    }
}

/* This leaks Dwarf_Error in case of error.  FIXME */
int
get_form_values(Dwarf_Debug dbg,Dwarf_Attribute attrib,
    Dwarf_Half * theform, Dwarf_Half * directform)
{
    Dwarf_Error verr = 0;
    int res = 0;

    res = dwarf_whatform(attrib, theform, &verr);
    DROP_ERROR_INSTANCE(dbg,res,verr);
    res = dwarf_whatform_direct(attrib, directform, &verr);
    DROP_ERROR_INSTANCE(dbg,res,verr);
    return res;
}

boolean
is_location_form(int form)
{
    if (form == DW_FORM_block1 ||
        form == DW_FORM_block2 ||
        form == DW_FORM_block4 ||
        form == DW_FORM_block ||
        form == DW_FORM_data4 ||
        form == DW_FORM_data8 ||
        form == DW_FORM_sec_offset) {
        return TRUE;
    }
    return FALSE;
}

/*  Fill buffer with location lists
    Buffer esbp expands as needed.
*/
void
get_location_list(Dwarf_Debug dbg,
    Dwarf_Die die,
    Dwarf_Attribute attr,
    char *esbp)
{
    Dwarf_Locdesc *llbuf = 0;
    Dwarf_Locdesc **llbufarray = 0; /* Only for older interface. */
    Dwarf_Unsigned no_of_elements;
    Dwarf_Loc_Head_c loclist_head = 0; /* 2015 loclist interface */
    Dwarf_Error llerr = 0;
    Dwarf_Unsigned i = 0;
    int lres = 0;
    unsigned llent = 0;

    /*  Base address used to update entries in .debug_loc.
        CU_base_address is a global. Terrible way to
        pass in this value. FIXME. See also CU_low_address
        as base address is special for address ranges */
    Dwarf_Addr base_address = CU_base_address;
    Dwarf_Addr lopc = 0;
    Dwarf_Addr hipc = 0;
    Dwarf_Bool bError = FALSE;
    Dwarf_Small lle_value = 0; /* DWARF5 */
    Dwarf_Small loclist_source = 0;
    /*  This is the section offset of the expression, not
        the location description prefix. */
    Dwarf_Unsigned section_offset = 0;
    Dwarf_Half elf_address_size = 0;
    Dwarf_Addr elf_max_address = 0;

    /* old and new interfaces differ on signedness.  */
    Dwarf_Signed locentry_count = 0;
    Dwarf_Unsigned ulocentry_count = 0;
    Dwarf_Bool checking = FALSE;

    if (!glflags.gf_use_old_dwarf_loclist) {
        lres = dwarf_get_loclist_c(attr,&loclist_head,
            &no_of_elements,&llerr);
        if (lres == DW_DLV_ERROR) {
            print_error(dbg, "dwarf_get_loclist_c", lres, llerr);
        } else if (lres == DW_DLV_NO_ENTRY) {
            return;
        }
    } else {
        Dwarf_Signed sno = 0;
        lres = dwarf_loclist_n(attr, &llbufarray, &sno, &llerr);
        if (lres == DW_DLV_ERROR) {
            print_error(dbg, "dwarf_loclist", lres, llerr);
        } else if (lres == DW_DLV_NO_ENTRY) {
            return;
        }
        no_of_elements = sno;
    }
    get_address_size_and_max(dbg,&elf_address_size,&elf_max_address,&llerr);
    for (llent = 0; llent < no_of_elements; ++llent) {
        char small_buf[150];
        Dwarf_Unsigned locdesc_offset = 0;
        Dwarf_Locdesc_c locentry = 0; /* 2015 */
        Dwarf_Addr lopcfinal = 0;
        Dwarf_Addr hipcfinal = 0;

        if (!glflags.gf_use_old_dwarf_loclist) {
            lres = dwarf_get_locdesc_entry_c(loclist_head,
                llent,
                &lle_value,
                &lopc, &hipc,
                &ulocentry_count,
                &locentry,
                &loclist_source,
                &section_offset,
                &locdesc_offset,
                &llerr);
            if (lres == DW_DLV_ERROR) {
                print_error(dbg, "dwarf_get_loclist_entry_c", lres, llerr);
            } else if (lres == DW_DLV_NO_ENTRY) {
                return;
            }
            locentry_count = ulocentry_count;
        } else {
            llbuf = llbufarray[llent];
            lopc = llbuf->ld_lopc;
            hipc = llbuf->ld_hipc;
            loclist_source = llbuf->ld_from_loclist;
            section_offset = llbuf->ld_section_offset;
            locdesc_offset = section_offset -
                sizeof(Dwarf_Half) - 2 * elf_address_size;
            locentry_count = llbuf->ld_cents;
            ulocentry_count = locentry_count;
            if (lopc == elf_max_address) {
                lle_value = DW_LLEX_base_address_selection_entry;
            } else if (lopc== 0 && hipc == 0) {
                lle_value = DW_LLEX_end_of_list_entry;
            } else {
                lle_value = DW_LLEX_offset_pair_entry;
            }
        }
        if (!dense && loclist_source) {
            if (llent == 0) {
                if (loclist_source == 1) {
                    snprintf(small_buf, sizeof(small_buf),
                        "<loclist at offset 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        " with %ld entries follows>",
                        locdesc_offset,
                        (long) no_of_elements);
                } else {
                    /* ASSERT: loclist_source == 2 */
                    snprintf(small_buf, sizeof(small_buf),
                        "<dwo loclist at offset 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        " with %ld entries follows>",
                        locdesc_offset,
                        (long) no_of_elements);
                }
                esb_append(esbp, small_buf);
            }
            esb_append(esbp, "\n\t\t\t");
            snprintf(small_buf, sizeof(small_buf), "[%2d]", llent);
            esb_append(esbp, small_buf);
        }


        /*  If we have a location list refering to the .debug_loc
            Check for specific compiler we are validating. */
        if ( glflags.gf_check_locations && in_valid_code &&
            loclist_source && checking_this_compiler()) {
            checking = TRUE;
        }
        /*  When dwarf_debug_addr_index_to_addr() fails
            it is probably DW_DLE_MISSING_NEEDED_DEBUG_ADDR_SECTION 257
            (because no TIED file supplied)
            but we don't distinguish that from other errors here. */
        if(loclist_source || checking) {
            /*  Simplifies to use the DWARF5 DW_LLE as the test.*/
            if (lle_value == DW_LLEX_base_address_selection_entry) {
                /*  (0xffffffff,addr), use specific address
                    (current PU address) */
                Dwarf_Addr realaddr = 0;
                if (loclist_source == 2) {
                    /*  hipc is index of a slot in .debug_addr section.
                        which contains base_address. */
                    int res = dwarf_debug_addr_index_to_addr(die,
                        hipc,&realaddr,&llerr);
                    if(res == DW_DLV_OK) {
                        base_address = realaddr;
                    } else if(res == DW_DLV_ERROR) {
                        snprintf(small_buf,sizeof(small_buf),
                            "<debug_addr index 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " %s>",hipc,
                            adexplain(dwarf_errno(llerr),
                            "base-address-unavailable"));
                        esb_append(esbp,small_buf);
                        base_address = 0;
                    } else {
                        snprintf(small_buf,sizeof(small_buf),
                            "<debug_addr index 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " no-entry finding index >",hipc);
                        esb_append(esbp,small_buf);
                        /* Cannot find .debug_addr */
                        base_address = 0;
                    }
                    snprintf(small_buf,sizeof(small_buf),
                        "<index to debug_addr : 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        " new base address 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        ">",
                        hipc,base_address);
                    esb_append(esbp,small_buf);
                } else {
                    base_address = hipc;
                    snprintf(small_buf,sizeof(small_buf),
                        "<new base address 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        ">",
                        base_address);
                    esb_append(esbp,small_buf);
                }
            } else if (lle_value == DW_LLEX_end_of_list_entry) {
                /* Nothing to do. */
                esb_append(esbp,"<end-of-list>");
            } else if (lle_value == DW_LLEX_start_length_entry) {
                int foundaddr = FALSE;
                if (loclist_source == 2) {
                    Dwarf_Addr realaddr = 0;
                    Dwarf_Addr slotindex = lopc;
                    /*  start (lopc) is index of a slot
                        in .debug_addr section. */
                    int res = dwarf_debug_addr_index_to_addr(die,
                        lopc,&realaddr,&llerr);
                    if(res == DW_DLV_OK) {
                        lopc = realaddr;
                        foundaddr = TRUE;
                    } else if(res == DW_DLV_ERROR) {
                        snprintf(small_buf,sizeof(small_buf),
                            "<debug_addr index 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " %s>",lopc,
                            adexplain(dwarf_errno(llerr),
                            "start-address-unavailable"));
                        esb_append(esbp,small_buf);
                    } else {
                        snprintf(small_buf,sizeof(small_buf),
                            "<debug_addr index 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " no-entry finding start index >",lopc);
                        esb_append(esbp,small_buf);
                        /* Cannot find .debug_addr */
                        lopc = 0;
                    }
                    snprintf(small_buf,sizeof(small_buf),
                        "<start-length index to debug_addr : 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        " addr  0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        " length 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        "> ",
                        slotindex,realaddr,hipc);
                    esb_append(esbp,small_buf);
                } else {
                    esb_append(esbp,"<Impossible start-length entry>");
                    /* Impossible */
                    lopc = 0;
                }
                lopcfinal = lopc;
                hipcfinal = lopcfinal + hipc;
                if (checking && foundaddr) {
                    loc_error_check(dbg,lopcfinal, lopc,
                        hipcfinal, hipc, locdesc_offset, base_address,
                        &bError);
                }
            } else if (lle_value == DW_LLEX_offset_pair_entry) {
                /* Same for both loclist_source. */
                lopcfinal = lopc + base_address;
                hipcfinal = hipc + base_address;
                snprintf(small_buf,sizeof(small_buf),
                    "< offset pair low-off : 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        " addr  0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        " high-off  0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        " addr 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        ">",
                        lopc,lopcfinal,hipc,hipcfinal);
                esb_append(esbp,small_buf);
                if(checking) {
                    loc_error_check(dbg,lopcfinal, lopc,
                        hipcfinal, hipc, locdesc_offset, base_address,
                        &bError);
                }
            } else if (lle_value == DW_LLEX_start_end_entry) {
                int foundaddr = FALSE;
                /* These are NOT relative to base_address */
                if (loclist_source == 2) {
                    /*  indices in .debug_addr of start and end
                        addresses. */
                    Dwarf_Addr reallo = 0;
                    Dwarf_Addr realhi = 0;
                    /* start is index of a slot in .debug_addr section. */
                    int res = dwarf_debug_addr_index_to_addr(die,
                        lopc,&reallo,&llerr);
                    if(res == DW_DLV_OK) {
                        lopcfinal = reallo;
                        foundaddr = TRUE;
                    } else if(res == DW_DLV_ERROR) {
                        snprintf(small_buf,sizeof(small_buf),
                            "<debug_addr index 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " %s>",lopc,
                            adexplain(dwarf_errno(llerr),
                            "start-address-unavailable"));
                        esb_append(esbp,small_buf);
                    } else {
                        snprintf(small_buf,sizeof(small_buf),
                            "<debug_addr index 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " error finding start index >",lopc);
                        esb_append(esbp,small_buf);
                        /* Cannot find .debug_addr */
                        lopcfinal = 0;
                    }
                    res = dwarf_debug_addr_index_to_addr(die,
                        hipc,&realhi,&llerr);
                    if(res == DW_DLV_OK) {
                        hipcfinal = realhi;
                    } else if(res == DW_DLV_ERROR) {
                        snprintf(small_buf,sizeof(small_buf),
                            "<debug_addr index 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " %s>",hipc,
                            adexplain(dwarf_errno(llerr),
                            "end-address-unavailable"));
                        esb_append(esbp,small_buf);
                        foundaddr = FALSE;
                    } else {
                        snprintf(small_buf,sizeof(small_buf),
                            "<debug_addr index 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " problem-finding-end-address >",hipc);
                        esb_append(esbp,small_buf);
                        /* Cannot find .debug_addr */
                        hipcfinal = 0;
                        foundaddr = FALSE;
                    }
                    snprintf(small_buf,sizeof(small_buf),
                        "< start-end low-index : 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " addr  0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " high-index  0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            " addr 0x%"
                            DW_PR_XZEROS DW_PR_DUx
                            ">",
                            lopc,lopcfinal,hipc,hipcfinal);
                    esb_append(esbp,small_buf);
                } else {
                    esb_append(esbp,"<Impossible start-end entry>");
                    /* Impossible */
                }
                if (checking && foundaddr) {
                    loc_error_check(dbg,lopcfinal, lopc,
                        hipcfinal, hipc, locdesc_offset, 0,
                        &bError);
                }
            } else {
                snprintf(small_buf,sizeof(small_buf),
                    "Unexpected LLEX code 0x%x, ERROR",lle_value);
                print_error(dbg, small_buf, DW_DLV_OK, llerr);
            }
            if (glflags.gf_display_offsets && verbose) {
                char *secname = ".debug_info";
                if(loclist_source == 1) {
                    secname = ".debug_loc";
                } else if (loclist_source == 2) {
                    secname = ".debug_loc.dwo";
                } else if (loclist_source) {
                    secname = "<unknown location entry code. ERROR.>";
                }

                snprintf(small_buf, sizeof(small_buf),
                    "<from %s offset 0x%" DW_PR_XZEROS  DW_PR_DUx ">",
                    secname,
                    locdesc_offset);
                esb_append(esbp, small_buf);

            }
        }
        dwarfdump_print_one_locdesc(dbg,
            /*  Either llbuf or locentry non-zero.
                Not both. */
            llbuf,
            locentry,
            llent, /* Which loc desc this is */
            locentry_count, /* How many ops in this loc desc */
            base_address,
            esbp);
    }

    if (bError &&  glflags.gf_check_verbose_mode) { // && PRINTING_UNIQUE) {
        printf("\n");
    }

    if (!glflags.gf_use_old_dwarf_loclist) {
        dwarf_loc_head_c_dealloc(loclist_head);
    } else {
        for (i = 0; i < no_of_elements; ++i) {
            dwarf_dealloc(dbg, llbufarray[i]->ld_s, DW_DLA_LOC_BLOCK);
            dwarf_dealloc(dbg, llbufarray[i], DW_DLA_LOCDESC);
        }
        dwarf_dealloc(dbg, llbufarray, DW_DLA_LIST);
    }
}

void
show_attr_form_error(Dwarf_Debug dbg,unsigned attr,
    unsigned form,
    char *out)
{
    const char *n = 0;
    int res = 0;
    char buf[30];
    Dwarf_Error formerr = 0;

    esb_append(out,"ERROR: Attribute ");
    snprintf(buf,sizeof(buf),"%u",attr);
    esb_append(out,buf);
    esb_append(out," (");
    res = dwarf_get_AT_name(attr,&n);
    if (res != DW_DLV_OK) {
        n = "UknownAttribute";
    }
    esb_append(out,n);
    esb_append(out,") ");
    esb_append(out," has form ");
    snprintf(buf,sizeof(buf),"%u",form);
    esb_append(out,buf);
    esb_append(out," (");
    res = dwarf_get_FORM_name(form,&n);
    if (res != DW_DLV_OK) {
        n = "UknownForm";
    }
    esb_append(out,n);
    esb_append(out,"), a form which is not appropriate");
    print_error_and_continue(dbg,esb_get_string(out), DW_DLV_OK,formerr);
}

/*
    Returns 1 if a proc with this low_pc found.
    Else returns 0.

    From print_die.c this has no pcMap passed in,
    we do not really have a sensible context, so this
    really just looks at the current attributes for a name.
*/
int
get_proc_name(Dwarf_Debug dbg, Dwarf_Die die, Dwarf_Addr low_pc,
    char *proc_name_buf, int proc_name_buf_len, void **pcMap)
{
    Dwarf_Signed atcnt = 0;
    Dwarf_Signed i = 0;
    Dwarf_Attribute *atlist = NULL;
    Dwarf_Addr low_pc_die = 0;
    int atres = 0;
    int funcres = 1;
    int funcpcfound = 0;
    int funcnamefound = 0;
    Dwarf_Error proc_name_err = 0;

    proc_name_buf[0] = 0;       /* always set to something */
    if (pcMap) {
        struct Addr_Map_Entry *ame = 0;
        ame = addr_map_find(low_pc,pcMap);
        if (ame && ame->mp_name) {
            /* mp_name is NULL only if we ran out of heap space. */
            safe_strcpy(proc_name_buf, proc_name_buf_len,
                ame->mp_name,(long) strlen(ame->mp_name));
            return 1;
        }
    }

    atres = dwarf_attrlist(die, &atlist, &atcnt, &proc_name_err);
    if (atres == DW_DLV_ERROR) {
        print_error(dbg, "dwarf_attrlist", atres, proc_name_err);
        return 0;
    }
    if (atres == DW_DLV_NO_ENTRY) {
        return 0;
    }
    for (i = 0; i < atcnt; i++) {
        Dwarf_Half attr = 0;
        int ares = 0;
        char * temps = 0;
        int sres = 0;
        int dres = 0;

        if (funcnamefound == 1 && funcpcfound == 1) {
            /* stop as soon as both found */
            break;
        }
        ares = dwarf_whatattr(atlist[i], &attr, &proc_name_err);
        if (ares == DW_DLV_ERROR) {
            load_CU_error_data(dbg,current_cu_die_for_print_frames);
            print_error(dbg, "get_proc_name whatattr error", ares, proc_name_err);
        } else if (ares == DW_DLV_OK) {
            switch (attr) {
            case DW_AT_specification:
            case DW_AT_abstract_origin:
                {
                    if (!funcnamefound) {
                        /*  Only use this if we have not seen DW_AT_name
                            yet .*/
                        int aores = get_abstract_origin_funcname(dbg,
                            atlist[i], proc_name_buf,proc_name_buf_len);
                        if (aores == DW_DLV_OK) {
                            /* FOUND THE NAME */
                            funcnamefound = 1;
                        }
                    }
                }
                break;
            case DW_AT_name:
                /*  Even if we saw DW_AT_abstract_origin, go ahead
                    and take DW_AT_name. */
                sres = dwarf_formstring(atlist[i], &temps, &proc_name_err);
                if (sres == DW_DLV_ERROR) {
                    load_CU_error_data(dbg, current_cu_die_for_print_frames);
                    print_error(dbg,
                        "formstring in get_proc_name failed",
                        sres, proc_name_err);
                    /*  50 is safe wrong length since is bigger than the
                        actual string */
                    safe_strcpy(proc_name_buf, proc_name_buf_len,
                        "ERROR in dwarf_formstring!", 50);
                } else if (sres == DW_DLV_NO_ENTRY) {
                    /*  50 is safe wrong length since is bigger than the
                        actual string */
                    safe_strcpy(proc_name_buf, proc_name_buf_len,
                        "NO ENTRY on dwarf_formstring?!", 50);
                } else {
                    long len = (long) strlen(temps);

                    safe_strcpy(proc_name_buf, proc_name_buf_len, temps,
                        len);
                }
                funcnamefound = 1;      /* FOUND THE NAME */
                break;
            case DW_AT_low_pc:
                dres = dwarf_formaddr(atlist[i], &low_pc_die, &proc_name_err);
                if (dres == DW_DLV_ERROR) {
                    load_CU_error_data(dbg, current_cu_die_for_print_frames);
                    if (DW_DLE_MISSING_NEEDED_DEBUG_ADDR_SECTION ==
                        dwarf_errno(proc_name_err)) {
                        print_error_and_continue(dbg,
                            "The .debug_addr section is missing, "
                            "low_pc unavailable",
                            dres,proc_name_err);
                        dwarf_dealloc(dbg,proc_name_err,DW_DLA_ERROR);
                        proc_name_err= 0;
                    } else {
                        print_error(dbg, "formaddr in get_proc_name failed",
                            dres, proc_name_err);
                    }
                    low_pc_die = ~low_pc;
                    /* ensure no match */
                }
                funcpcfound = 1;

                break;
            default:
                break;
            }
        }
    }
    for (i = 0; i < atcnt; i++) {
        dwarf_dealloc(dbg, atlist[i], DW_DLA_ATTR);
    }
    dwarf_dealloc(dbg, atlist, DW_DLA_LIST);
    if (funcnamefound && funcpcfound && pcMap ) {
        /*  Insert every name to map, not just the one
            we are looking for.
            This version does extra work in that
            early symbols in a CU will be inserted
            multiple times (the extra times have no
            effect), the dwarfdump2
            version of this does less work.  */
        addr_map_insert(low_pc_die,proc_name_buf,pcMap);
    }
    if (funcnamefound == 0 || funcpcfound == 0 || low_pc != low_pc_die) {
        funcres = 0;
    }
    return (funcres);
}

/*  Print CU basic information but
    use the local DIE for the offsets. */
void PRINT_CU_INFO(void)
{
    Dwarf_Unsigned loff = DIE_offset;
    Dwarf_Unsigned goff = DIE_overall_offset;
    char lbuf[50];
    char hbuf[50];

    if (current_section_id == DEBUG_LINE ||
        current_section_id == DEBUG_FRAME ||
        current_section_id == DEBUG_FRAME_EH_GNU ||
        current_section_id == DEBUG_ARANGES ||
        current_section_id == DEBUG_MACRO ||
        current_section_id == DEBUG_MACINFO ) {
        /*  These sections involve the CU die, so
            use the CU offsets.
            The DEBUG_MAC* cases are logical but
            not yet useful (Dec 2015).
            In other cases the local DIE offset makes
            more sense. */
        loff = DIE_CU_offset;
        goff = DIE_CU_overall_offset;
    }
    if (!cu_data_is_set()) {
        return;
    }
    printf("\n");
    // printf("CU Name = %s\n",sanitized(CU_name));
    // printf("CU Producer = %s\n",sanitized(CU_producer));
    printf("CU Name = %s\n", CU_name);
    printf("CU Producer = %s\n", CU_producer);

    printf("DIE OFF = 0x%" DW_PR_XZEROS DW_PR_DUx
        " GOFF = 0x%" DW_PR_XZEROS DW_PR_DUx,
        loff,goff);
    /* We used to print leftover and incorrect values at times. */
    if ( need_CU_high_address) {
        strcpy(hbuf,"unknown   ");
    } else {
        snprintf(hbuf,sizeof(hbuf),
            "0x%"  DW_PR_XZEROS DW_PR_DUx,CU_high_address);
    }
    if ( need_CU_base_address) {
        strcpy(lbuf,"unknown   ");
    } else {
        snprintf(lbuf,sizeof(lbuf),
            "0x%"  DW_PR_XZEROS DW_PR_DUx,CU_low_address);
    }
#if 0 /* Old format print */
    printf(", Low PC = 0x%08" DW_PR_DUx ", High PC = 0x%08" DW_PR_DUx ,
        CU_low_address,CU_high_address);
#endif
    printf(", Low PC = %s, High PC = %s", lbuf,hbuf);
    printf("\n");
}

/*  Are we checking for errors from the
    compiler of the current compilation unit?
*/
boolean
checking_this_compiler(void)
{
    /*  This flag has been update by 'update_compiler_target()'
        and indicates if the current CU is in a targeted compiler
        specified by the user. Default value is TRUE, which
        means test all compilers until a CU is detected. */
    // return current_cu_is_checked_compiler;
    return TRUE;
}

static const char *
adexplain(Dwarf_Unsigned liberr,
   const char * alterr)
{
    if (liberr == DW_DLE_MISSING_NEEDED_DEBUG_ADDR_SECTION) {
        return  "no-tied-debug-addr-available";
    }
    return alterr;
}

static void
loc_error_check(Dwarf_Debug dbg,
    Dwarf_Addr lopcfinal,
    Dwarf_Addr lopc,
    Dwarf_Addr hipcfinal,
    Dwarf_Addr hipc,
    Dwarf_Unsigned offset,
    Dwarf_Addr base_address,
    Dwarf_Bool *bError)
{
    // DWARF_CHECK_COUNT(locations_result,1);

    /*  Check the low_pc and high_pc are within
        a valid range in the .text section */
    if (IsValidInBucketGroup(pRangesInfo,lopcfinal) &&
        IsValidInBucketGroup(pRangesInfo,hipcfinal)) {
        /* Valid values; do nothing */
    } else {
        /*  At this point may be we are dealing with
            a linkonce symbol */
        if (IsValidInLinkonce(pLinkonceInfo,PU_name,
            lopcfinal,hipcfinal)) {
            /* Valid values; do nothing */
        } else {
            *bError = TRUE;
            // DWARF_CHECK_ERROR(locations_result,
            //     ".debug_loc: Address outside a "
            //     "valid .text range");
            // if ( glflags.gf_check_verbose_mode) { && PRINTING_UNIQUE) {
                printf(
                    "Offset = 0x%" DW_PR_XZEROS DW_PR_DUx
                    ", Base = 0x%"  DW_PR_XZEROS DW_PR_DUx ", "
                    "Low = 0x%"  DW_PR_XZEROS DW_PR_DUx
                    " (0x%"  DW_PR_XZEROS DW_PR_DUx
                    "), High = 0x%"  DW_PR_XZEROS DW_PR_DUx
                    " (0x%"  DW_PR_XZEROS DW_PR_DUx ")\n",
                    offset,base_address,lopcfinal,
                    lopc,
                    hipcfinal,
                    hipc);
            // }
        }
    }
}

void
print_error_and_continue(Dwarf_Debug dbg,
    const char * msg,
    int dwarf_code,
    Dwarf_Error lerr)
{
    print_error_maybe_continue(dbg,
        msg,dwarf_code,lerr,TRUE);
}

void
record_range_array_info_entry(Dwarf_Off die_off,Dwarf_Off range_off)
{
    /* Record a new detected range info. */
    if (range_array_count == range_array_size) {
        /* Resize range array */
        range_array_size *= 2;
        range_array = (Range_Array_Entry *)
            realloc(range_array,
            (range_array_size) * sizeof(Range_Array_Entry));
    }
    /* The 'die_off' is the Global Die Offset */
    range_array[range_array_count].die_off = die_off;
    range_array[range_array_count].range_off = range_off;
    ++range_array_count;
}

void
print_ranges_list_to_extra(Dwarf_Debug dbg,
    Dwarf_Unsigned off,
    Dwarf_Ranges *rangeset,
    Dwarf_Signed rangecount,
    Dwarf_Unsigned bytecount,
    char *stringbuf)
{
    int res = 0;
    char tmp[200];
    const char * sec_name = 0;
    Dwarf_Signed i = 0;
    Dwarf_Error err =0;


    res = dwarf_get_ranges_section_name(dbg,&sec_name,&err);
    if(res != DW_DLV_OK ||  !sec_name || !strlen(sec_name)) {
        sec_name = ".debug_ranges";
    }

    if (dense) {
        snprintf(tmp,sizeof(tmp),
            "< ranges: %" DW_PR_DSd " ranges at %s offset %"
            DW_PR_DUu " (0x%" DW_PR_XZEROS DW_PR_DUx ") "
            "(%" DW_PR_DUu " bytes)>",
            rangecount,
            sec_name,
            off,
            off,
            bytecount);
        esb_append(stringbuf,tmp);
    } else {
        snprintf(tmp,sizeof(tmp),
            "\t\tranges: %" DW_PR_DSd " at %s offset %"
            DW_PR_DUu " (0x%" DW_PR_XZEROS DW_PR_DUx ") "
            "(%" DW_PR_DUu " bytes)\n",
            rangecount,
            sec_name,
            off,
            off,
            bytecount);
        esb_append(stringbuf,tmp);
    }
    for (i = 0; i < rangecount; ++i) {
        Dwarf_Ranges * r = rangeset +i;
        const char *type = get_rangelist_type_descr(r);
        if (dense) {
            snprintf(tmp,sizeof(tmp),
                "<[%2" DW_PR_DSd
                "] %s 0x%" DW_PR_XZEROS  DW_PR_DUx
                " 0x%" DW_PR_XZEROS DW_PR_DUx ">",
                (Dwarf_Signed)i,
                type,
                (Dwarf_Unsigned)r->dwr_addr1,
                (Dwarf_Unsigned)r->dwr_addr2);
        } else {
            snprintf(tmp,sizeof(tmp),
                "\t\t\t[%2" DW_PR_DSd
                "] %-14s 0x%" DW_PR_XZEROS  DW_PR_DUx
                " 0x%" DW_PR_XZEROS DW_PR_DUx "\n",
                (Dwarf_Signed)i,
                type,
                (Dwarf_Unsigned)r->dwr_addr1,
                (Dwarf_Unsigned)r->dwr_addr2);
        }
        esb_append(stringbuf,tmp);
    }
}

static const char *
get_rangelist_type_descr(Dwarf_Ranges *r)
{
    switch (r->dwr_type) {
    case DW_RANGES_ENTRY:             return "range entry";
    case DW_RANGES_ADDRESS_SELECTION: return "addr selection";
    case DW_RANGES_END:               return "range end";
    }
    /* Impossible. */
    return "Unknown";
}

boolean
is_strstrnocase(const char * container, const char * contained)
{
    const unsigned char *ct = (const unsigned char *)container;
    for (; *ct; ++ct )
    {
        const unsigned char * cntnd = (const unsigned char *)contained;

        for (; *cntnd && *ct ; ++cntnd,++ct)
        {
            unsigned char lct = tolower(*ct);
            unsigned char tlc = tolower(*cntnd);
            if (lct != tlc) {
                break;
            }
        }
        if (!*cntnd) {
            /* We matched all the way to end of contained  */
            /* ASSERT: innerwrong = FALSE  */
            return TRUE;
        }
        if (!*ct) {
            /*  Ran out of container before contained,
                so no future match of contained
                is possible. */
            return FALSE;

        }
        /*  No match so far.
            See if there is more in container to check. */
    }
    return FALSE;
}

/* For inlined functions, try to find name */
static int
get_abstract_origin_funcname(Dwarf_Debug dbg, Dwarf_Attribute attr,
    char *name_out, unsigned maxlen)
{
    Dwarf_Off off = 0;
    Dwarf_Die origin_die = 0;
    Dwarf_Attribute *atlist = NULL;
    Dwarf_Signed atcnt = 0;
    Dwarf_Signed i = 0;
    int dres = 0;
    int atres = 0;
    int name_found = 0;
    int res = 0;
    Dwarf_Error err = 0;

    res = dwarf_global_formref(attr,&off,&err);
    if (res != DW_DLV_OK) {
        return DW_DLV_NO_ENTRY;
    }
    dres = dwarf_offdie(dbg,off,&origin_die,&err);
    if (dres != DW_DLV_OK) {
        return DW_DLV_NO_ENTRY;
    }
    atres = dwarf_attrlist(origin_die, &atlist, &atcnt, &err);
    if (atres != DW_DLV_OK) {
        dwarf_dealloc(dbg,origin_die,DW_DLA_DIE);
        return DW_DLV_NO_ENTRY;
    }
    for (i = 0; i < atcnt; i++) {
        Dwarf_Half lattr = 0;
        int ares = 0;

        ares = dwarf_whatattr(atlist[i], &lattr, &err);
        if (ares == DW_DLV_ERROR) {
            break;
        } else if (ares == DW_DLV_OK) {
            if (lattr == DW_AT_name) {
                int sres = 0;
                char* temps = 0;
                sres = dwarf_formstring(atlist[i], &temps, &err);
                if (sres == DW_DLV_OK) {
                    long len = (long) strlen(temps);
                    safe_strcpy(name_out, maxlen, temps, len);
                    name_found = 1;
                    break;
                }
            }
        }
    }
    for (i = 0; i < atcnt; i++) {
        dwarf_dealloc(dbg, atlist[i], DW_DLA_ATTR);
    }
    dwarf_dealloc(dbg, atlist, DW_DLA_LIST);
    dwarf_dealloc(dbg,origin_die,DW_DLA_DIE);
    if (!name_found) {
        return DW_DLV_NO_ENTRY;
    }
    return DW_DLV_OK;
}

static boolean
cu_data_is_set(void)
{
    if (strcmp(CU_name,default_cu_producer) ||
        strcmp(CU_producer,default_cu_producer)) {
        return 1;
    }
    if (DIE_offset  || DIE_overall_offset) {
        return 1;
    }
    if (CU_base_address || CU_low_address || CU_high_address) {
        return 1;
    }
    return 0;
}

/*  This attempts to provide some data for error messages when
    reading frame/eh-frame data.
    On failure just give up here and return.
    Other code will be reporting an error, in this function
    we do not report such.
    Setting these globals as much as possible:
    CU_name CU_producer DIE_CU_offset  DIE_CU_overall_offset
    CU_base_address CU_high_address
    Using DW_AT_low_pc, DW_AT_high_pc,DW_AT_name
    DW_AT_producer.
  */
static void
load_CU_error_data(Dwarf_Debug dbg, Dwarf_Die cu_die)
{
    Dwarf_Signed atcnt = 0;
    Dwarf_Attribute *atlist = 0;
    Dwarf_Half tag = 0;
    char **srcfiles = 0;
    Dwarf_Signed srccnt = 0;
    int local_show_form_used = 0;
    int local_verbose = 0;
    int atres = 0;
    Dwarf_Signed i = 0;
    Dwarf_Signed k = 0;
    Dwarf_Error loadcuerr = 0;
    Dwarf_Off cu_die_goff = 0;

    if(!cu_die) {
        return;
    }
    atres = dwarf_attrlist(cu_die, &atlist, &atcnt, &loadcuerr);
    if (atres != DW_DLV_OK) {
        /*  Something is seriously wrong if it is DW_DLV_ERROR. */
        DROP_ERROR_INSTANCE(dbg,atres,loadcuerr);
        return;
    }
    atres = dwarf_tag(cu_die, &tag, &loadcuerr);
    if (atres != DW_DLV_OK) {
        for (k = 0; k < atcnt; k++) {
            dwarf_dealloc(dbg, atlist[k], DW_DLA_ATTR);
        }
        dwarf_dealloc(dbg, atlist, DW_DLA_LIST);
        /*  Something is seriously wrong if it is DW_DLV_ERROR. */
        DROP_ERROR_INSTANCE(dbg,atres,loadcuerr);
        return;
    }

    /* The offsets will be zero if it fails. Let it pass. */
    atres = dwarf_die_offsets(cu_die,&DIE_overall_offset,
        &DIE_offset,&loadcuerr);
    cu_die_goff = DIE_overall_offset;
    DROP_ERROR_INSTANCE(dbg,atres,loadcuerr);

    DIE_CU_overall_offset = DIE_overall_offset;
    DIE_CU_offset = DIE_offset;
    for (i = 0; i < atcnt; i++) {
        Dwarf_Half attr = 0;
        int ares = 0;
        Dwarf_Attribute attrib = atlist[i];

        ares = dwarf_whatattr(attrib, &attr, &loadcuerr);
        if (ares != DW_DLV_OK) {
            for (k = 0; k < atcnt; k++) {
                dwarf_dealloc(dbg, atlist[k], DW_DLA_ATTR);
            }
            dwarf_dealloc(dbg, atlist, DW_DLA_LIST);
            DROP_ERROR_INSTANCE(dbg,ares,loadcuerr);
            return;
        }
        /*  For now we will not fully deal with the complexity of
            DW_AT_high_pc being an offset of low pc. */
        switch(attr) {
        case DW_AT_low_pc:
            {
            ares = dwarf_formaddr(attrib, &CU_base_address, &loadcuerr);
            DROP_ERROR_INSTANCE(dbg,ares,loadcuerr);
            CU_low_address = CU_base_address;
            }
            break;
        case DW_AT_high_pc:
            {
            /*  This is wrong for DWARF4 instances where
                the attribute is really an offset.
                It's also useless for CU DIEs that do not
                have the DW_AT_high_pc high so CU_high_address will
                be zero*/
            ares = dwarf_formaddr(attrib, &CU_high_address, &loadcuerr);
            DROP_ERROR_INSTANCE(dbg,ares,loadcuerr);
            }
            break;
        case DW_AT_name:
        case DW_AT_producer:
            {
            const char *name = 0;
            // struct esb_s namestr;
            char namestr[ESB_S_CHAR_LENGTH];

            esb_constructor(namestr);
            get_attr_value(dbg, tag, cu_die,
                cu_die_goff,attrib, srcfiles, srccnt,
                namestr, local_show_form_used,local_verbose);
            name = esb_get_string(namestr);
            if(attr == DW_AT_name) {
                safe_strcpy(CU_name,sizeof(CU_name),name,strlen(name));
            } else {
                safe_strcpy(CU_producer,sizeof(CU_producer),name,strlen(name));
            }
            // esb_destructor(&namestr);
            }
            break;
        default:
            /* do nothing */
            break;
        }
    }
    for (k = 0; k < atcnt; k++) {
        dwarf_dealloc(dbg, atlist[k], DW_DLA_ATTR);
    }
    dwarf_dealloc(dbg, atlist, DW_DLA_LIST);
}

/*  A strcpy which ensures NUL terminated string
    and never overruns the output.
*/
void
safe_strcpy(char *out, long outlen, const char *in, long inlen)
{
    if (inlen >= (outlen - 1)) {
        strncpy(out, in, outlen - 1);
        out[outlen - 1] = 0;
    } else {
        strcpy(out, in);
    }
}

/*  *data is presumed to contain garbage, not values, and
    is properly initialized here. */
void
esb_constructor(char *data)
{
    memset(data, 0, 1);
}

void
print_line_numbers_this_cu(Dwarf_Debug dbg, Dwarf_Die cu_die)
{
    Dwarf_Unsigned lineversion = 0;
    Dwarf_Signed linecount = 0;
    Dwarf_Line *linebuf = NULL;
    Dwarf_Signed linecount_actuals = 0;
    Dwarf_Line *linebuf_actuals = NULL;
    Dwarf_Small  table_count = 0;
    int lres = 0;
    Dwarf_Line_Context line_context = 0;
    const char *sec_name = 0;
    Dwarf_Error err = 0;
    Dwarf_Off cudie_local_offset = 0;
    Dwarf_Off dieprint_cu_goffset = 0;
    int atres = 0;

    current_section_id = DEBUG_LINE;

    /* line_flag is TRUE */


    lres = dwarf_get_line_section_name_from_die(cu_die,
        &sec_name,&err);
    if (lres != DW_DLV_OK || !sec_name || !strlen(sec_name)) {
        sec_name = ".debug_line";
    }
    /* The offsets will be zero if it fails. Let it pass. */
    atres = dwarf_die_offsets(cu_die,&dieprint_cu_goffset,
        &cudie_local_offset,&err);
    DROP_ERROR_INSTANCE(dbg,atres,err);

    if (glflags.gf_do_print_dwarf) {
        printf("\n%s: line number info for a single cu\n", sec_name);
    } else {
        /* We are checking, not printing. */
        Dwarf_Half tag = 0;
        int tres = dwarf_tag(cu_die, &tag, &err);
        if (tres != DW_DLV_OK) {
            /*  Something broken here. */
            print_error(dbg,"Unable to see CU DIE tag "
                "though we could see it earlier. Something broken.",
                tres,err);
            return;
        } else if (tag == DW_TAG_type_unit) {
            /*  Not checking since type units missing
                address or range in CU header. */
            return;
        }
    }

    /*  The following is complicated by a desire to test
        various line table interface functions.  Hence
        we test line_flag_selection.

        Normal code should pick an interface
        (for most  the best choice is what we here call
        glflags.gf_line_flag_selection ==  singledw5)
        and use just that interface set.

        Sorry about the length of the code that
        results from having so many interfaces.  */
    if (glflags.gf_line_flag_selection ==  singledw5) {
        lres = dwarf_srclines_b(cu_die,&lineversion,
            &table_count,&line_context,
            &err);
        if(lres == DW_DLV_OK) {
            lres = dwarf_srclines_from_linecontext(line_context,
                &linebuf, &linecount,&err);
        }
    } else if (glflags.gf_line_flag_selection == orig) {
        /* DWARF2,3,4, ok for 5. */
        /* Useless for experimental line tables */
        lres = dwarf_srclines(cu_die,
            &linebuf, &linecount, &err);
        if(lres == DW_DLV_OK && linecount ){
            table_count++;
        }
    } else if (glflags.gf_line_flag_selection == orig2l) {
        lres = dwarf_srclines_two_level(cu_die,
            &lineversion,
            &linebuf, &linecount,
            &linebuf_actuals, &linecount_actuals,
            &err);
        if(lres == DW_DLV_OK && linecount){
            table_count++;
        }
        if(lres == DW_DLV_OK && linecount_actuals){
            table_count++;
        }
    } else if (glflags.gf_line_flag_selection == s2l) {
        lres = dwarf_srclines_b(cu_die,&lineversion,
            &table_count,&line_context,
            &err);
        if(lres == DW_DLV_OK) {
            lres = dwarf_srclines_two_level_from_linecontext(line_context,
                &linebuf, &linecount,
                &linebuf_actuals, &linecount_actuals,
                &err);
        }
    }
    if (lres == DW_DLV_ERROR) {
        /* Do not terminate processing */
        // if (glflags.gf_check_decl_file) {
        //     DWARF_CHECK_COUNT(decl_file_result,1);
        //     DWARF_CHECK_ERROR2(decl_file_result,"dwarf_srclines",
        //         dwarf_errmsg(err));
        //     glflags.gf_record_dwarf_error = FALSE;  /* Clear error condition */
        // } else {
        //     print_error(dbg, "dwarf_srclines", lres, err);
        // }
    } else if (lres == DW_DLV_NO_ENTRY) {
        /* no line information is included */
    } else if (table_count > 0) {
        /* DW_DLV_OK */
        if (glflags.gf_do_print_dwarf) {
            if(line_context && verbose) {
                print_line_context_record(dbg,line_context);
            }
            print_source_intro(dbg,cu_die);
            // if (verbose) {
            //     print_one_die(dbg, cu_die,
            //         dieprint_cu_goffset,
            //         /* print_information= */ TRUE,
            //         /* indent_level= */ 0,
            //         /* srcfiles= */ 0, /* cnt= */ 0,
            //         /* ignore_die_stack= */TRUE);
            // }
        }
        if(glflags.gf_line_flag_selection ==  singledw5 || glflags.gf_line_flag_selection == s2l) {
            if (table_count == 0 || table_count == 1) {
                /* ASSERT: is_single_table == true */
                Dwarf_Bool is_logicals = FALSE;
                Dwarf_Bool is_actuals = FALSE;
                process_line_table(dbg,sec_name, linebuf, linecount,
                    is_logicals,is_actuals);
            } else {
                Dwarf_Bool is_logicals = TRUE;
                Dwarf_Bool is_actuals = FALSE;
                process_line_table(dbg,sec_name, linebuf, linecount,
                    is_logicals, is_actuals);
                process_line_table(dbg,sec_name, linebuf_actuals,
                    linecount_actuals,
                    !is_logicals, !is_actuals);
            }
            dwarf_srclines_dealloc_b(line_context);
        } else if (glflags.gf_line_flag_selection == orig) {
            Dwarf_Bool is_logicals = FALSE;
            Dwarf_Bool is_actuals = FALSE;
            process_line_table(dbg,sec_name, linebuf, linecount,
                is_logicals, is_actuals);
            dwarf_srclines_dealloc(dbg,linebuf,linecount);
        } else if (glflags.gf_line_flag_selection == orig2l) {
            if (table_count == 1 || table_count == 0) {
                Dwarf_Bool is_logicals = FALSE;
                Dwarf_Bool is_actuals = FALSE;
                process_line_table(dbg,sec_name, linebuf, linecount,
                    is_logicals, is_actuals);
            } else {
                Dwarf_Bool is_logicals = TRUE;
                Dwarf_Bool is_actuals = FALSE;
                process_line_table(dbg,sec_name, linebuf, linecount,
                    is_logicals, is_actuals);
                process_line_table(dbg,sec_name,
                    linebuf_actuals, linecount_actuals,
                    !is_logicals, !is_actuals);
            }
            dwarf_srclines_dealloc(dbg,linebuf,linecount);
        }
        /* end, table_count > 0 */
    } else {
        /* DW_DLV_OK */
        /*  table_count == 0. no lines in table.
            Just a line table header. */
        if (glflags.gf_do_print_dwarf) {
            int ores = 0;
            Dwarf_Unsigned off = 0;

            print_source_intro(dbg,cu_die);
            // if (verbose) {
            //     print_one_die(dbg, cu_die,
            //         dieprint_cu_goffset,
            //         /* print_information= */ TRUE,
            //         /* indent_level= */ 0,
            //         /* srcfiles= */ 0, /* cnt= */ 0,
            //         /* ignore_die_stack= */TRUE);
            // }
            if(line_context) {
                if (verbose > 2) {
                    print_line_context_record(dbg,line_context);
                }
                ores = dwarf_srclines_table_offset(line_context,
                    &off,&err);
                if (ores != DW_DLV_OK) {
                    print_error(dbg,"dwarf_srclines_table_offset fail",ores,err);
                } else {
                    printf(" Line table is present (offset 0x%"
                        DW_PR_XZEROS DW_PR_DUx
                        ") but no lines present\n", off);
                }
            } else {
                printf(" Line table is present but no lines present\n");
            }
        }
        if(glflags.gf_line_flag_selection ==  singledw5 ||
            glflags.gf_line_flag_selection == s2l) {
            dwarf_srclines_dealloc_b(line_context);
        } else {
            /* Original allocation. */
            dwarf_srclines_dealloc(dbg,linebuf,linecount);
        }
        /* end, linecounttotal == 0 */
    }
}

static void
print_source_intro(Dwarf_Debug dbg,Dwarf_Die cu_die)
{
    int         ores = 0;
    Dwarf_Off   off = 0;
    Dwarf_Error src_err = 0;

    ores = dwarf_dieoffset(cu_die, &off, &src_err);
    if (ores == DW_DLV_OK) {
        int lres = 0;
        const char *sec_name = 0;

        lres = dwarf_get_die_section_name_b(cu_die,
            &sec_name,&src_err);
        if (lres != DW_DLV_OK ||  !sec_name || !strlen(sec_name)) {
            sec_name = ".debug_info";
        }
        printf("Source lines (from CU-DIE at %s offset 0x%"
            DW_PR_XZEROS DW_PR_DUx "):\n",
            sec_name,
            (Dwarf_Unsigned) off);
        if (lres == DW_DLV_ERROR) {
            dwarf_dealloc(dbg,src_err, DW_DLA_ERROR);
            src_err = 0;
        }
    } else {
        if (ores == DW_DLV_ERROR) {
            dwarf_dealloc(dbg,src_err, DW_DLA_ERROR);
            src_err = 0;
        }
        printf("Source lines (for the CU-DIE at unknown location):\n");
    }
}

/* Here we test the interfaces into Dwarf_Line_Context. */
static void
print_line_context_record(Dwarf_Debug dbg,
    Dwarf_Line_Context line_context)
{
    int vres = 0;
    Dwarf_Unsigned lsecoff = 0;
    Dwarf_Unsigned version = 0;
    Dwarf_Signed count = 0;
    Dwarf_Signed i = 0;
    const char *name = 0;
    Dwarf_Small table_count = 0;
    Dwarf_Error err = 0;
    char bufr[ESB_S_CHAR_LENGTH];

    esb_constructor(bufr);
    printf("Line Context data\n");
    vres = dwarf_srclines_table_offset(line_context,&lsecoff,&err);
    if (vres != DW_DLV_OK) {
        print_error(dbg,"Error accessing line context"
            "Something broken.",
            vres,err);
        return;
    }
    printf(" Line Section Offset 0x%"
        DW_PR_XZEROS DW_PR_DUx "\n", lsecoff);
    vres = dwarf_srclines_version(line_context,&version,
        &table_count, &err);
    if (vres != DW_DLV_OK) {
        print_error(dbg,"Error accessing line context"
            "Something broken.",
            vres,err);
        return;
    }
    printf(" version number      0x%" DW_PR_DUx " %" DW_PR_DUu "\n",
        version,version);
    printf(" number of line tables  %d.\n", table_count);


    vres = dwarf_srclines_comp_dir(line_context,&name,&err);
    if (vres != DW_DLV_OK) {
        print_error(dbg,"Error accessing line context"
            "Something broken.",
            vres,err);
        return;
    }
    if (name) {
        printf(" Compilation directory: %s\n",name);
    } else {
        printf(" Compilation directory: <unknown no DW_AT_comp_dir>\n");
    }

    vres = dwarf_srclines_include_dir_count(line_context,&count,&err);
    if (vres != DW_DLV_OK) {
        print_error(dbg,"Error accessing line context"
            "Something broken.",
            vres,err);
        return;
    }
    printf(" include directory count 0x%"
        DW_PR_DUx " %" DW_PR_DSd "\n",
        (Dwarf_Unsigned)count,count);
    for(i = 1; i <= count; ++i) {
        vres = dwarf_srclines_include_dir_data(line_context,i,
            &name,&err);
        if (vres != DW_DLV_OK) {
            print_error(dbg,"Error accessing line context"
                "Something broken.",
                vres,err);
            return;
        }
        printf("  [%2" DW_PR_DSd "]  \"%s\"\n",i,name);
    }

    vres = dwarf_srclines_files_count(line_context,&count,&err);
    if (vres != DW_DLV_OK) {
        print_error(dbg,"Error accessing line context"
            "Something broken.",
            vres,err);
        return;
    }
    printf( " files count 0x%"
        DW_PR_DUx " %" DW_PR_DUu "\n",
        count,count);
    for(i = 1; i <= count; ++i) {
        Dwarf_Unsigned dirindex = 0;
        Dwarf_Unsigned modtime = 0;
        Dwarf_Unsigned flength = 0;

        vres = dwarf_srclines_files_data(line_context,i,
            &name,&dirindex, &modtime,&flength,&err);
        if (vres != DW_DLV_OK) {
            print_error(dbg,"Error accessing line context"
                "Something broken.",
                vres,err);
            return;
        }
        esb_empty_string(bufr);
        if (name) {
            esb_empty_string(bufr);
            esb_append(bufr,"\"");
            esb_append(bufr,name);
            esb_append(bufr,"\"");
        } else {
            esb_append(bufr,"<ERROR:NULL name in files list>");
        }
        printf("  [%2" DW_PR_DSd "]  %-24s ,",
            i,esb_get_string(bufr));
        printf(" directory index  %2" DW_PR_DUu ,dirindex);
        printf(",  file length %2" DW_PR_DUu ,flength);
        if (modtime) {
            time_t tt3 = (time_t)modtime;

            /* ctime supplies newline */
            // printf(
            //     "file mod time 0x%x %s", (unsigned)tt3, ctime(&tt3));
            printf(
                "file mod time 0x%x now", (unsigned) tt3);    
        } else {
            printf("  file mod time 0\n");
        }
    }
    // esb_destructor(&bufr);

    vres = dwarf_srclines_subprog_count(line_context,&count,&err);
    if (vres != DW_DLV_OK) {
        print_error(dbg,"Error accessing line context"
            "Something broken.",
            vres,err);
        return;
    }
    if (count == 0) {
        return;
    }
    printf(" subprograms count (experimental) 0x%"
        DW_PR_DUx " %" DW_PR_DUu "\n",
        count,count);
    for(i = 1; i <= count; ++i) {
        Dwarf_Unsigned decl_file = 0;
        Dwarf_Unsigned decl_line = 0;
        vres = dwarf_srclines_subprog_data(line_context,i,
            &name,&decl_file, &decl_line,&err);
        if (vres != DW_DLV_OK) {
            print_error(dbg,"Error accessing line context"
                "Something broken.",
                vres,err);
            return;
        }
        printf("  [%2" DW_PR_DSd "]  \"%s\""
            ", fileindex %2" DW_PR_DUu
            ", lineindex  %2" DW_PR_DUu
            "\n",
            i,name,decl_file,decl_line);
    }
}

static void
process_line_table(Dwarf_Debug dbg,
    const char *sec_name,
    Dwarf_Line *linebuf, Dwarf_Signed linecount,
    Dwarf_Bool is_logicals_table, Dwarf_Bool is_actuals_table)
{
    char *padding = 0;
    Dwarf_Signed i = 0;
    Dwarf_Addr pc = 0;
    Dwarf_Unsigned lineno = 0;
    Dwarf_Unsigned logicalno = 0;
    Dwarf_Unsigned column = 0;
    Dwarf_Unsigned call_context = 0;
    char* subprog_name = 0;
    char* subprog_filename = 0;
    Dwarf_Unsigned subprog_line = 0;

    Dwarf_Error lt_err = 0;

    Dwarf_Bool newstatement = 0;
    Dwarf_Bool lineendsequence = 0;
    Dwarf_Bool new_basic_block = 0;
    int sres = 0;
    int ares = 0;
    int lires = 0;
    int cores = 0;
    Dwarf_Addr elf_max_address = 0;
    char lastsrc[ESB_S_CHAR_LENGTH];

    esb_constructor(lastsrc);
    current_section_id = DEBUG_LINE;

    /* line_flag is TRUE */
    get_address_size_and_max(dbg,0,&elf_max_address,&lt_err);
    /* Padding for a nice layout */
    padding = glflags.gf_line_print_pc ? "            " : "";
    if (glflags.gf_do_print_dwarf) {
        /* Check if print of <pc> address is needed. */
        printf("\n");
        if (is_logicals_table) {
            printf("Logicals Table:\n");
            printf("%sNS new statement, PE prologue end, "
                "EB epilogue begin\n",padding);
            printf("%sDI=val discriminator value\n",
                padding);
            printf("%sCC=val context, SB=val subprogram\n",
                padding);
        } else if (is_actuals_table) {
            printf("Actuals Table:\n");
            printf("%sBB new basic block, ET end of text sequence\n"
                "%sIS=val ISA number\n",padding,padding);

        } else {
            /* Standard DWARF line table. */
            printf("%sNS new statement, BB new basic block, "
                "ET end of text sequence\n",padding);
            printf("%sPE prologue end, EB epilogue begin\n",padding);
            printf("%sIS=val ISA number, DI=val discriminator value\n",
                padding);
        }
        if (is_logicals_table || is_actuals_table) {
            printf("[ row]  ");
        }
        if (glflags.gf_line_print_pc) {
            printf("<pc>        ");
        }
        if (is_logicals_table) {
            printf("[lno,col] NS PE EB DI= CC= SB= uri: \"filepath\"\n");
        } else if (is_actuals_table) {
            printf("[logical] BB ET IS=\n");
        } else {
            printf("[lno,col] NS BB ET PE EB IS= DI= uri: \"filepath\"\n");
        }
    }
    for (i = 0; i < linecount; i++) {
        Dwarf_Line line = linebuf[i];
        char* filename = 0;
        int nsres = 0;
        Dwarf_Bool found_line_error = FALSE;
        char *where = NULL;

        filename = "<unknown>";
        if (!is_actuals_table) {
            sres = dwarf_linesrc(line, &filename, &lt_err);
            if (sres == DW_DLV_ERROR) {
                /* Do not terminate processing */
                where = "dwarf_linesrc()";
                record_line_error(where,lt_err);
                found_line_error = TRUE;
            }
        }

        pc = 0;
        ares = dwarf_lineaddr(line, &pc, &lt_err);

        if (ares == DW_DLV_ERROR) {
            /* Do not terminate processing */
            where = "dwarf_lineaddr()";
            record_line_error(where,lt_err);
            found_line_error = TRUE;
            pc = 0;
        }
        if (ares == DW_DLV_NO_ENTRY) {
            pc = 0;
        }

        if (is_actuals_table) {
            lires = dwarf_linelogical(line, &logicalno, &lt_err);
            if (lires == DW_DLV_ERROR) {
                /* Do not terminate processing */
                where = "dwarf_linelogical()";
                record_line_error(where,lt_err);
                found_line_error = TRUE;
            }
            if (lires == DW_DLV_NO_ENTRY) {
                logicalno = -1LL;
            }
            column = 0;
        } else {
            lires = dwarf_lineno(line, &lineno, &lt_err);
            if (lires == DW_DLV_ERROR) {
                /* Do not terminate processing */
                where = "dwarf_lineno()";
                record_line_error(where,lt_err);
                found_line_error = TRUE;
            }
            if (lires == DW_DLV_NO_ENTRY) {
                lineno = -1LL;
            }
            cores = dwarf_lineoff_b(line, &column, &lt_err);
            if (cores == DW_DLV_ERROR) {
                /* Do not terminate processing */
                where = "dwarf_lineoff()";
                record_line_error(where,lt_err);
                found_line_error = TRUE;
            }
            if (cores == DW_DLV_NO_ENTRY) {
                /*  Zero was always the correct default, meaning
                    the left edge. DWARF2/3/4 spec sec 6.2.2 */
                column = 0;
            }
        }

        /* Display the error information */
        if (found_line_error || glflags.gf_record_dwarf_error) {
            glflags.gf_record_dwarf_error = FALSE;
            /* Due to a fatal error, skip current record */
            if (found_line_error) {
                continue;
            }
        }
        if (glflags.gf_do_print_dwarf) {
            if (is_logicals_table || is_actuals_table) {
                printf("[%4" DW_PR_DUu "]  ", i + 1);
            }
            /* Check if print of <pc> address is needed. */
            if (glflags.gf_line_print_pc) {
                printf("0x%" DW_PR_XZEROS DW_PR_DUx "  ", pc);
            }
            if (is_actuals_table) {
                printf("[%7" DW_PR_DUu "]", logicalno);
            } else {
                printf("[%4" DW_PR_DUu ",%2" DW_PR_DUu "]", lineno, column);
            }
        }

        if (!is_actuals_table) {
            nsres = dwarf_linebeginstatement(line, &newstatement, &lt_err);
            if (nsres == DW_DLV_OK) {
                if (newstatement && glflags.gf_do_print_dwarf) {
                    printf(" %s","NS");
                }
            } else if (nsres == DW_DLV_ERROR) {
                print_error(dbg, "linebeginstatment failed", nsres, lt_err);
            }
        }

        if (!is_logicals_table) {
            nsres = dwarf_lineblock(line, &new_basic_block, &lt_err);
            if (nsres == DW_DLV_OK) {
                if (new_basic_block && glflags.gf_do_print_dwarf) {
                    printf(" %s","BB");
                }
            } else if (nsres == DW_DLV_ERROR) {
                print_error(dbg, "lineblock failed", nsres, lt_err);
            }
            nsres = dwarf_lineendsequence(line, &lineendsequence, &lt_err);
            if (nsres == DW_DLV_OK) {
                if (lineendsequence && glflags.gf_do_print_dwarf) {
                    printf(" %s", "ET");
                }
            } else if (nsres == DW_DLV_ERROR) {
                print_error(dbg, "lineendsequence failed", nsres, lt_err);
            }
        }

        if (glflags.gf_do_print_dwarf) {
            Dwarf_Bool prologue_end = 0;
            Dwarf_Bool epilogue_begin = 0;
            Dwarf_Unsigned isa = 0;
            Dwarf_Unsigned discriminator = 0;
            int disres = dwarf_prologue_end_etc(line,
                &prologue_end,&epilogue_begin,
                &isa,&discriminator,&lt_err);
            if (disres == DW_DLV_ERROR) {
                print_error(dbg, "dwarf_prologue_end_etc() failed",
                    disres, lt_err);
            }
            if (prologue_end && !is_actuals_table) {
                printf(" PE");
            }
            if (epilogue_begin && !is_actuals_table) {
                printf(" EB");
            }
            if (isa && !is_logicals_table) {
                printf(" IS=0x%" DW_PR_DUx, isa);
            }
            if (discriminator && !is_actuals_table) {
                printf(" DI=0x%" DW_PR_DUx, discriminator);
            }
            if (is_logicals_table) {
                call_context = 0;
                disres = dwarf_linecontext(line, &call_context, &lt_err);
                if (disres == DW_DLV_ERROR) {
                    print_error(dbg, "dwarf_linecontext() failed",
                        disres, lt_err);
                }
                if (call_context) {
                    printf(" CC=%" DW_PR_DUu, call_context);
                }
                subprog_name = 0;
                disres = dwarf_line_subprog(line, &subprog_name,
                    &subprog_filename, &subprog_line, &lt_err);
                if (disres == DW_DLV_ERROR) {
                    print_error(dbg, "dwarf_line_subprog() failed",
                        disres, lt_err);
                }
                if (subprog_name && strlen(subprog_name)) {
                    /*  We do not print an empty name.
                        Clutters things up. */
                    // printf(" SB=\"%s\"", sanitized(subprog_name));
                    printf(" SB=\"%s\"", subprog_name);
                }
            }
        }

        if (!is_actuals_table) {
            if (i > 0 &&  verbose < 3  &&
                strcmp(filename,esb_get_string(lastsrc)) == 0) {
                /* Do not print name. */
            } else {
                char urs[ESB_S_CHAR_LENGTH];
                esb_constructor(urs);
                esb_append(urs, " uri: \"");
                translate_to_uri(filename, urs);
                esb_append(urs,"\"");
                if (glflags.gf_do_print_dwarf) {
                    printf("%s",esb_get_string(urs));
                }
                // esb_destructor(urs);
                esb_empty_string(lastsrc);
                esb_append(lastsrc,filename);
            }
            if (sres == DW_DLV_OK) {
                dwarf_dealloc(dbg, filename, DW_DLA_STRING);
            }
        }

        if (glflags.gf_do_print_dwarf) {
            printf("\n");
        }
    }
    // esb_destructor(&lastsrc);
}

static void
record_line_error(const char *where, Dwarf_Error line_err)
{
    char tmp_buff[500];
    if (glflags.gf_check_lines) { //  && checking_this_compiler()) {
        snprintf(tmp_buff, sizeof(tmp_buff),
            "Error getting line details calling %s dwarf error is %s",
            where,dwarf_errmsg(line_err));
        // DWARF_CHECK_ERROR(lines_result,tmp_buff);
    }
}

/* Translate dangerous and some other characters to safe
   %xx form.
*/
void
translate_to_uri(const char * filename, char *out)
{
    char buf[8];
    const char *cp = 0;
    for (cp = filename  ; *cp; ++cp) {
        char v[2];
        int c = 0xff & (unsigned char)*cp;
        if (dwarfdump_ctype_table[c]) {
            v[0] = c;
            v[1] = 0;
            esb_append(out,v);
        } else {
            char *b = xchar(c,buf,sizeof(buf));
            esb_append(out,b);
        }
    }
}
