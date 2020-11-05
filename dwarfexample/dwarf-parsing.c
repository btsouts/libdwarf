#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>

#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>

// #include "dwarf.h"
// #include "libdwarf.h"
#include "dwarf-parsing.h"

#include "../dwarfdump/naming.h"

typedef struct linkedLibsList linkedLibsList;

struct linkedLibsList
{
	char					name[COMPILATION_UNIT_STR_LEN];
    linkedLibsList		    *next;
};

typedef struct firstParseCUsList firstParseCUsList;

struct firstParseCUsList
{
	uint32_t				cuGOffset;
    firstParseCUsList		*next;
};

/*  Allocate variables for lists    */
static compilationUnitList     *compilationUnitsHead=NULL, *compilationUnitsTail=NULL;
static baseTypesList           *baseTypesHead=NULL, *baseTypesTail=NULL;
static subProgramsList         *subProgramsHead=NULL, *subProgramsTail=NULL;
static firstParseCUsList       *firstParseCUsHead=NULL, *firstParseCUsTail=NULL;

extern boolean show_form_used;
extern int verbose;

static uint32_t
lookUpBaseTypeEncoding(baseTypesList *baseTypesListHead, uint32_t targetGOffset);

static void
getTypeForVariable(baseTypesList *baseTypesListHead, variablesList *targetVariable, uint32_t targetGOffset);

static void
getTypeForSubProgram(baseTypesList *baseTypesListHead, subProgramsList *targetSubProgram, uint32_t targetGOffset);

static void
getCompilationUnitAttributes(Dwarf_Debug dbg, Dwarf_Die print_me,
    Dwarf_Off dieprint_cu_goffset, int level, struct srcfilesdata *sf,
    Dwarf_Attribute *atlist, Dwarf_Signed atcnt);

static void
getSubProgramAttributes(Dwarf_Debug dbg, Dwarf_Die print_me,
    Dwarf_Off dieprint_cu_goffset, int level, struct srcfilesdata *sf,
    Dwarf_Attribute *atlist, Dwarf_Signed atcnt);

static void
getLocalVariablesAttributes(Dwarf_Debug dbg, Dwarf_Die print_me,
    Dwarf_Off dieprint_cu_goffset, int level, struct srcfilesdata *sf,
    Dwarf_Attribute *atlist, Dwarf_Signed atcnt, variablesList *variablesListTail, int isLocalScope);

static void
getVariableTypeAttributes(Dwarf_Debug dbg, Dwarf_Die print_me,
    Dwarf_Off dieprint_cu_goffset, int level, struct srcfilesdata *sf,
    Dwarf_Attribute *atlist, Dwarf_Signed atcnt, baseTypesList *baseTypeNode, int isPointer);

// static int
// isDeclaration(Dwarf_Debug dbg, Dwarf_Die print_me,
//     Dwarf_Attribute *atlist, Dwarf_Signed atcnt, int isLocalScope);

/*  Lookup the encoding type of a variable or pointer type, according to its global offset. */
/*  If the search fails, then it returns 0x00   */
static uint32_t
lookUpBaseTypeEncoding(baseTypesList *baseTypesListHead, uint32_t targetGOffset)
{
    baseTypesList   *oneBaseType = baseTypesListHead;

    while ((oneBaseType != NULL) && (oneBaseType->globalOffset != targetGOffset))
    {
        // printf("oneBaseType->globalOffset: 0x%X, targetGOffset: 0x%X\n", oneBaseType->globalOffset, targetGOffset);
        
        oneBaseType = oneBaseType->next;
    }

    if (oneBaseType == NULL)
    {
        return 0x00; /* Not found   */
    }
    else
    {
        return oneBaseType->encoding;
    }
}

static void
getTypeForVariable(baseTypesList *baseTypesListHead, variablesList *targetVariable, uint32_t targetGOffset)
{
    baseTypesList   *oneBaseType = baseTypesListHead;

    while ((oneBaseType != NULL) && (oneBaseType->globalOffset != targetGOffset))
    {
        // printf("oneBaseType->globalOffset: 0x%X, targetGOffset: 0x%X\n", oneBaseType->globalOffset, targetGOffset);
        
        oneBaseType = oneBaseType->next;
    }

    if (oneBaseType == NULL)
    {
        // return 0x00; /* Not found   */
    }
    else
    {
        // return oneBaseType->encoding;

        if (oneBaseType->isPointer)
        {
            targetVariable->isPointer = 1;

            /*  Delegate this choice to when the pointer type is created    */
            targetVariable->isFloatingPoint = oneBaseType->isFloatingPoint;

            // getTypeForVariable(baseTypesListHead, targetVariable, oneBaseType->pointerTypeGOffset)
        }
        else
        {
            targetVariable->isPointer = 0;

            targetVariable->isFloatingPoint = oneBaseType->isFloatingPoint;
        }
    }
}

static void
getTypeForSubProgram(baseTypesList *baseTypesListHead, subProgramsList *targetSubProgram, uint32_t targetGOffset)
{
    baseTypesList   *oneBaseType = baseTypesListHead;

    while ((oneBaseType != NULL) && (oneBaseType->globalOffset != targetGOffset))
    {
        // printf("oneBaseType->globalOffset: 0x%X, targetGOffset: 0x%X\n", oneBaseType->globalOffset, targetGOffset);
        
        oneBaseType = oneBaseType->next;
    }

    if (oneBaseType == NULL)
    {
        // return 0x00; /* Not found   */
    }
    else
    {
        // return oneBaseType->encoding;

        if (oneBaseType->isPointer)
        {
            targetSubProgram->isPointer = 1;

            /*  Delegate this choice to when the pointer type is created    */
            targetSubProgram->isFloatingPoint = oneBaseType->isFloatingPoint;

            // getTypeForVariable(baseTypesListHead, targetVariable, oneBaseType->pointerTypeGOffset)
        }
        else
        {
            targetSubProgram->isPointer = 0;

            targetSubProgram->isFloatingPoint = oneBaseType->isFloatingPoint;
        }
    }
}

static void
getCompilationUnitAttributes(Dwarf_Debug dbg, Dwarf_Die print_me,
    Dwarf_Off dieprint_cu_goffset, int level, struct srcfilesdata *sf,
    Dwarf_Attribute *atlist, Dwarf_Signed atcnt)
{
    Dwarf_Error podie_err = 0;
    Dwarf_Attribute attrib = 0;
    int tres = 0;
    Dwarf_Half tag = 0;
    Dwarf_Error paerr = 0;
    char lesb[ESB_S_CHAR_LENGTH];
    Dwarf_Unsigned uval = 0;

    for (int i = 0; i < atcnt; i++) 
    {
        Dwarf_Half attr;
        int ares;

        ares = dwarf_whatattr(atlist[i], &attr, &podie_err);

        attrib = atlist[i];

        if (ares == DW_DLV_OK) {
            switch (attr) 
            {
                case DW_AT_low_pc:
                case DW_AT_high_pc:
                    {
                        Dwarf_Half theform;
                        int rv;
                        int res = 0;
                        Dwarf_Addr addr = 0;

                        rv = dwarf_whatform(attrib,&theform,&paerr);
                        /*  Depending on the form and the attribute,
                            process the form. */
                        if (rv == DW_DLV_ERROR) {
                            print_error(dbg, "dwarf_whatform cannot Find attr form",
                                rv, paerr);
                        } else if (rv == DW_DLV_NO_ENTRY) {
                            break;
                        }

                        // printf("getCompilationUnitAttributes: theform: 0x%X\n", theform);
                        
                        if (theform != DW_FORM_addr &&
                            theform != DW_FORM_GNU_addr_index &&
                            theform != DW_FORM_addrx) 
                        {
                            res = get_small_encoding_integer_and_name(dbg,
                                attrib,
                                &uval,
                                /* attrname */ (const char *) NULL,
                                /* err_string */ ( char *) NULL,
                                (encoding_type_func) 0,
                                &paerr, show_form_used);

                            // printf("getCompilationUnitAttributes: uval: %llu\n", uval);
                        }
                        else
                        {
                            res = dwarf_formaddr(attrib, &addr, &paerr);

                            // printf("getCompilationUnitAttributes: addr: 0x%llX\n", addr);
                        }
                        
                        // esb_constructor(lesb);

                        // get_attr_value(dbg, tag, print_me,
                        //     dieprint_cu_goffset,
                        //     attrib, sf->srcfiles, sf->srcfilescount,
                        //     lesb, show_form_used, verbose);

                        // printf("getCompilationUnitAttributes: DW_AT_pc: %s\n", lesb);

                        if(res == DW_DLV_OK) 
                        {
                            if (attr == DW_AT_low_pc) 
                            {
                                compilationUnitsTail->lowPC = addr;
#ifdef PRINT_DEBUG_MESSAGES
                                printf("getCompilationUnitAttributes: Compilation Unit Low PC: 0x%X\n", compilationUnitsTail->lowPC);
#endif                                
                            } 
                            else 
                            { /* DW_AT_high_pc */
                                compilationUnitsTail->highPC = compilationUnitsTail->lowPC + uval;
#ifdef PRINT_DEBUG_MESSAGES
                                printf("getCompilationUnitAttributes: Compilation Unit High PC: 0x%X (Offset: 0x%llX)\n", compilationUnitsTail->highPC, uval);
#endif                                
                            }
                        }
                        else
                        {
                            printf("getCompilationUnitAttributes: res: %d\n", res);
                        }
                    }
                    break;
                case DW_AT_name:
                case DW_AT_GNU_template_name:
                    tres = dwarf_tag(print_me, &tag, &paerr);

                    if (tres == DW_DLV_ERROR) {
                        tag = 0;
                    } else if (tres == DW_DLV_NO_ENTRY) {
                        tag = 0;
                    } else {
                        /* ok */
                    }
                    
                    esb_constructor(compilationUnitsTail->name);
                    
                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount,
                        compilationUnitsTail->name, show_form_used, verbose);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getCompilationUnitAttributes: Compilation Unit Name: %s\n", compilationUnitsTail->name);
#endif                    
                    break;

                case DW_AT_producer:
                    esb_constructor(lesb);

                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount,
                        lesb, show_form_used, verbose);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getCompilationUnitAttributes: DW_AT_producer: %s\n", lesb);
#endif
                    break;   
                case DW_AT_language:
                    esb_constructor(lesb);

                    get_small_encoding_integer_and_name(dbg, attrib, &uval,
                        "DW_AT_language", lesb,
                        get_LANG_name, &paerr,
                        show_form_used);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getCompilationUnitAttributes: DW_AT_language: %s\n", lesb);
#endif   
                    break;
                case DW_AT_stmt_list:
                    esb_constructor(lesb);

                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount, 
                        lesb, show_form_used,verbose);

#ifdef PRINT_DEBUG_MESSAGES                    
                    printf("getCompilationUnitAttributes: DW_AT_stmt_list: %s\n", lesb);
#endif
                    break; 
                case DW_AT_comp_dir:
                    esb_constructor(lesb);

                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount, 
                        lesb, show_form_used,verbose);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getCompilationUnitAttributes: DW_AT_comp_dir: %s\n", lesb);
#endif                    
                    break; 
                default:
#ifdef PRINT_DEBUG_MESSAGES                
                    printf("getCompilationUnitAttributes: Skipped attribute: 0x%X\n", attr);
#endif
                    break;
            }
        }
        else
        { 
            print_error(dbg, "dwarf_whatattr entry missing", ares, podie_err);
        }
    }
}

static void
getSubProgramAttributes(Dwarf_Debug dbg, Dwarf_Die print_me,
    Dwarf_Off dieprint_cu_goffset, int level, struct srcfilesdata *sf,
    Dwarf_Attribute *atlist, Dwarf_Signed atcnt)
{
    Dwarf_Error podie_err = 0;
    Dwarf_Attribute attrib = 0;
    int tres = 0;
    int res = 0;
    Dwarf_Half tag = 0;
    Dwarf_Error paerr = 0;
    char lesb[ESB_S_CHAR_LENGTH];
    Dwarf_Unsigned uval = 0;

    for (int i = 0; i < atcnt; i++) 
    {
        Dwarf_Half attr;
        int ares;

        ares = dwarf_whatattr(atlist[i], &attr, &podie_err);

        attrib = atlist[i];

        if (ares == DW_DLV_OK) {
            switch (attr) 
            {
                case DW_AT_low_pc:
                case DW_AT_high_pc:
                    {
                        Dwarf_Half theform;
                        int rv;
                        Dwarf_Addr addr = 0;

                        rv = dwarf_whatform(attrib,&theform,&paerr);
                        /*  Depending on the form and the attribute,
                            process the form. */
                        if (rv == DW_DLV_ERROR) {
                            print_error(dbg, "dwarf_whatform cannot Find attr form",
                                rv, paerr);
                        } else if (rv == DW_DLV_NO_ENTRY) {
                            break;
                        }

                        // printf("getCompilationUnitAttributes: theform: 0x%X\n", theform);
                        
                        if (theform != DW_FORM_addr &&
                            theform != DW_FORM_GNU_addr_index &&
                            theform != DW_FORM_addrx) 
                        {
                            res = get_small_encoding_integer_and_name(dbg,
                                attrib,
                                &uval,
                                /* attrname */ (const char *) NULL,
                                /* err_string */ ( char *) NULL,
                                (encoding_type_func) 0,
                                &paerr, show_form_used);

                            // printf("getCompilationUnitAttributes: uval: %llu\n", uval);
                        }
                        else
                        {
                            res = dwarf_formaddr(attrib, &addr, &paerr);

                            // printf("getCompilationUnitAttributes: addr: 0x%llX\n", addr);
                        }
                        
                        // esb_constructor(lesb);

                        // get_attr_value(dbg, tag, print_me,
                        //     dieprint_cu_goffset,
                        //     attrib, sf->srcfiles, sf->srcfilescount,
                        //     lesb, show_form_used, verbose);

                        // printf("getCompilationUnitAttributes: DW_AT_pc: %s\n", lesb);

                        if(res == DW_DLV_OK) 
                        {
                            if (attr == DW_AT_low_pc) 
                            {
                                subProgramsTail->lowPC = addr;
#ifdef PRINT_DEBUG_MESSAGES                            
                                printf("getSubProgramAttributes: Sub Program Low PC: 0x%X\n", subProgramsTail->lowPC);
#endif                                
                            } 
                            else 
                            { /* DW_AT_high_pc */
                                subProgramsTail->highPC = subProgramsTail->lowPC + uval;
#ifdef PRINT_DEBUG_MESSAGES
                                printf("getSubProgramAttributes: Sub Program High PC: 0x%X (Offset: 0x%llX)\n", subProgramsTail->highPC, uval);
#endif                                
                            }
                        }
                        else
                        {
                            printf("getSubProgramAttributes: res: %d\n", res);
                        }
                    }
                    break;
                case DW_AT_name:
                case DW_AT_GNU_template_name:
                    tres = dwarf_tag(print_me, &tag, &paerr);

                    if (tres == DW_DLV_ERROR) {
                        tag = 0;
                    } else if (tres == DW_DLV_NO_ENTRY) {
                        tag = 0;
                    } else {
                        /* ok */
                    }
                    
                    esb_constructor(subProgramsTail->name);
                    
                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount,
                        subProgramsTail->name, show_form_used,verbose);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getSubProgramAttributes: Sub Program Name: %s\n", subProgramsTail->name);
#endif                    
                    break;

                case DW_AT_producer:
                    esb_constructor(lesb);

                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount,
                        lesb, show_form_used,verbose);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getSubProgramAttributes: DW_AT_producer: %s\n", lesb);
#endif
                    break;   
                case DW_AT_language:
                    esb_constructor(lesb);

                    get_small_encoding_integer_and_name(dbg, attrib, &uval,
                        "DW_AT_language", lesb,
                        get_LANG_name, &paerr,
                        show_form_used);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getSubProgramAttributes: DW_AT_language: %s\n", lesb);
#endif   
                    break;
                case DW_AT_stmt_list:
                    esb_constructor(lesb);

                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount, 
                        lesb, show_form_used,verbose);

#ifdef PRINT_DEBUG_MESSAGES                    
                    printf("getSubProgramAttributes: DW_AT_stmt_list: %s\n", lesb);
#endif
                    break; 
                case DW_AT_comp_dir:
                    esb_constructor(lesb);

                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount, 
                        lesb, show_form_used,verbose);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getSubProgramAttributes: DW_AT_comp_dir: %s\n", lesb);
#endif                    
                    break;
                case DW_AT_type:
                {
                    Dwarf_Off ref_goff = 0;

                    res = dwarf_global_formref(attrib, &ref_goff, &paerr);

                    subProgramsTail->typeGlobalOffset = ref_goff;

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getSubProgramAttributes: Type GOFF: 0x%X\n", subProgramsTail->typeGlobalOffset);
#endif
                    /*  Check the type of type  */
                }

                    break;
                case DW_AT_decl_column:
                case DW_AT_decl_file:
                case DW_AT_decl_line:
                {
                    // esb_constructor(subProgramsTail->);
                    esb_constructor(lesb);

                    res = get_small_encoding_integer_and_name(dbg,
                        attrib,
                        &uval,
                        /* attrname */ (const char *) NULL,
                        /* err_string */ ( char *) NULL,
                        (encoding_type_func) 0,
                        &paerr, show_form_used);

                    if (res == DW_DLV_OK) {
                        Dwarf_Bool hex_format = TRUE;
                        formx_unsigned(uval, lesb, hex_format);
                        /* Check attribute encoding */
                        // if (glflags.gf_check_attr_encoding) {
                            // check_attributes_encoding(attr,theform,tempud);
                        // }

                        if (attr == DW_AT_decl_file || attr == DW_AT_call_file) {
                            if (sf->srcfiles && uval > 0 &&
                                /* ASSERT: cnt >= 0 */
                                uval <= (Dwarf_Unsigned) sf->srcfilescount) {
                                /*  added by user request */
                                /*  srcfiles is indexed starting at 0, but
                                    DW_AT_decl_file defines that 0 means no
                                    file, so tempud 1 means the 0th entry in
                                    srcfiles, thus tempud-1 is the correct
                                    index into srcfiles.  */
                                char *fname = sf->srcfiles[uval - 1];

                                esb_append(lesb, " ");
                                esb_append(lesb, fname);
                            }
                        }

                        if (attr == DW_AT_decl_column)
                        {
#ifdef PRINT_DEBUG_MESSAGES                            
                            printf("getSubProgramAttributes: DW_AT_decl_column: 0x%llX\n", uval);
#endif                            
                        }
                        else if (attr == DW_AT_decl_file)
                        {
#ifdef PRINT_DEBUG_MESSAGES                           
                            printf("getSubProgramAttributes: DW_AT_decl_file: 0x%s\n", lesb);
#endif                            
                        }
                        else if (attr == DW_AT_decl_line)
                        {
#ifdef PRINT_DEBUG_MESSAGES                            
                            printf("getSubProgramAttributes: DW_AT_decl_line: 0x%llX\n", uval);
#endif                            
                        }
                        else
                        {
                            printf("getSubProgramAttributes: Unknown state\n");
                        }
                        
                    } else {
                        print_error(dbg, "Cannot get encoding attribute ..",
                            res, paerr);
                    }
                }
                    break;
                case DW_AT_frame_base:
                    {
                        /*  The value is a location description
                            or location list. */

                        Dwarf_Half theform = 0;
                        Dwarf_Half directform = 0;

                        esb_constructor(lesb);
                        
                        get_form_values(dbg,attrib, &theform, &directform);
                        
                        if (is_location_form(theform)) {
#ifdef PRINT_DEBUG_MESSAGES                            
                            printf("getSubProgramAttributes: DW_AT_frame_base is_location_form\n");
#endif
                            get_location_list(dbg, print_me, attrib, lesb);
                            show_form_itself(show_form_used, verbose,
                                theform, directform, lesb);
                        } else if (theform == DW_FORM_exprloc)  {
                            /* int showhextoo = 1; */
                            print_exprloc_content(dbg, print_me, attrib, 1, lesb);
                        } else {
                            show_attr_form_error(dbg, attr, theform, lesb);
                        }

#ifdef PRINT_DEBUG_MESSAGES
                        printf("getSubProgramAttributes: DW_AT_frame_base: %s\n", lesb);
#endif
                    }

                    break;                    
                default:
#ifdef PRINT_DEBUG_MESSAGES                
                    printf("getSubProgramAttributes: Skipped attribute: 0x%X\n", attr);
#endif
                    break;
            }
        }
        else
        { 
            print_error(dbg, "dwarf_whatattr entry missing", ares, podie_err);
        }
    }
}

static void
getLocalVariablesAttributes(Dwarf_Debug dbg, Dwarf_Die print_me,
    Dwarf_Off dieprint_cu_goffset, int level, struct srcfilesdata *sf,
    Dwarf_Attribute *atlist, Dwarf_Signed atcnt, variablesList *variablesListTail, int isLocalScope)
{
    Dwarf_Error podie_err = 0;
    Dwarf_Attribute attrib = 0;
    int tres = 0;
    int res = 0;
    Dwarf_Half tag = 0;
    Dwarf_Error paerr = 0;
    char lesb[ESB_S_CHAR_LENGTH];
    Dwarf_Unsigned uval = 0;

    for (int i = 0; i < atcnt; i++) 
    {
        Dwarf_Half attr;
        int ares;

        ares = dwarf_whatattr(atlist[i], &attr, &podie_err);

        attrib = atlist[i];

        if (ares == DW_DLV_OK) {
            switch (attr) 
            {
                case DW_AT_name:
                case DW_AT_GNU_template_name:
                    tres = dwarf_tag(print_me, &tag, &paerr);

                    if (tres == DW_DLV_ERROR) {
                        tag = 0;
                    } else if (tres == DW_DLV_NO_ENTRY) {
                        tag = 0;
                    } else {
                        /* ok */
                    }
                    
                    esb_constructor(variablesListTail->name);
                    
                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount,
                        variablesListTail->name, show_form_used, verbose);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getLocalVariablesAttributes: Variable Name: %s\n", variablesListTail->name);
#endif                    
                    break;
                case DW_AT_type:
                {
                    Dwarf_Off ref_goff = 0;

                    res = dwarf_global_formref(attrib, &ref_goff, &paerr);

                    variablesListTail->typeGlobalOffset = ref_goff;

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getLocalVariablesAttributes: Type GOFF: 0x%X\n", variablesListTail->typeGlobalOffset );
#endif
                    // getTypeForVariable(baseTypesHead, variablesListTail, ref_goff);

                    // printf("getLocalVariablesAttributes: isPointer: %d isFloatingPoint: %d\n", 
                    //     variablesListTail->isPointer,variablesListTail->isFloatingPoint);
                }

                    break;
                case DW_AT_decl_column:
                case DW_AT_decl_file:
                case DW_AT_decl_line:
                {
                    // esb_constructor(subProgramsTail->);
                    esb_constructor(lesb);

                    res = get_small_encoding_integer_and_name(dbg,
                        attrib,
                        &uval,
                        /* attrname */ (const char *) NULL,
                        /* err_string */ ( char *) NULL,
                        (encoding_type_func) 0,
                        &paerr, show_form_used);

                    if (res == DW_DLV_OK) {
                        Dwarf_Bool hex_format = TRUE;
                        formx_unsigned(uval, lesb, hex_format);
                        
                        /* Check attribute encoding */
                        // if (glflags.gf_check_attr_encoding) {
                            // check_attributes_encoding(attr,theform,tempud);
                        // }

                        if (attr == DW_AT_decl_file || attr == DW_AT_call_file) {
                            if (sf->srcfiles && uval > 0 &&
                                /* ASSERT: cnt >= 0 */
                                uval <= (Dwarf_Unsigned) sf->srcfilescount) {
                                /*  added by user request */
                                /*  srcfiles is indexed starting at 0, but
                                    DW_AT_decl_file defines that 0 means no
                                    file, so tempud 1 means the 0th entry in
                                    srcfiles, thus tempud-1 is the correct
                                    index into srcfiles.  */
                                char *fname = sf->srcfiles[uval - 1];

                                esb_append(lesb, " ");
                                esb_append(lesb, fname);
                            }
                        }

                        if (attr == DW_AT_decl_column)
                        {
#ifdef PRINT_DEBUG_MESSAGES                            
                            printf("getLocalVariablesAttributes: DW_AT_decl_column: 0x%llX\n", uval);
#endif                            
                        }
                        else if (attr == DW_AT_decl_file)
                        {
#ifdef PRINT_DEBUG_MESSAGES                            
                            printf("getLocalVariablesAttributes: DW_AT_decl_file: 0x%s\n", lesb);
#endif                            
                        }
                        else if (attr == DW_AT_decl_line)
                        {
#ifdef PRINT_DEBUG_MESSAGES
                            printf("getLocalVariablesAttributes: DW_AT_decl_line: 0x%llX\n", uval);
#endif                            
                        }
                        else
                        {
                            printf("getLocalVariablesAttributes: Unknown state\n");
                        }
                        
                    } else {
                        print_error(dbg, "Cannot get encoding attribute ..",
                            res, paerr);
                    }
                }
                    break;
                case DW_AT_declaration:
                    /*  for extern variables -- skip for now    */
                    break;                    
                case DW_AT_external:
                {
                    Dwarf_Half theform = 0;
                    // esb_constructor(lesb);
                    
                    // get_attr_value(dbg, tag, print_me,
                    //     dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount,
                    //     lesb, show_form_used, verbose);
                    res = dwarf_whatform(attrib, &theform, &paerr);

                    /*  Depending on the form and the attribute, process the form. */
                    if (res == DW_DLV_ERROR) 
                    {
                        print_error(dbg, "dwarf_whatform cannot Find Attr Form", res, paerr);
                    } 
                    else if (res == DW_DLV_NO_ENTRY) 
                    {
                        printf("getLocalVariablesAttributes: DW_AT_external: DW_DLV_NO_ENTRY\n");
                    }

                    if (theform == DW_FORM_flag_present)
                    {
                        if (isLocalScope)
                        {
                            printf("getLocalVariablesAttributes: Non global scope but DW_AT_external 1\n");   
                        }
                        
                        variablesListTail->isExternal = 1;
#ifdef PRINT_DEBUG_MESSAGES
                        printf("getLocalVariablesAttributes: DW_AT_external: 1\n");   
#endif                        
                    }
                    else
                    {
                        printf("getLocalVariablesAttributes: Unknown theform: 0x%X\n", theform);
                    }
                }

                    break;
                case DW_AT_location:
                case DW_AT_frame_base:
                    {
                        /*  The value is a location description
                            or location list. */

                        Dwarf_Half theform = 0;
                        Dwarf_Half directform = 0;
                        Dwarf_Ptr x = 0;

                        esb_constructor(lesb);
                        
                        get_form_values(dbg, attrib, &theform, &directform);
                        
                        if (is_location_form(theform)) {
#ifdef PRINT_DEBUG_MESSAGES                            
                            printf("getLocalVariablesAttributes: DW_AT_location is_location_form\n");
#endif
                            get_location_list(dbg, print_me, attrib, lesb);
                            show_form_itself(show_form_used, verbose,
                                theform, directform, lesb);
                        } else if (theform == DW_FORM_exprloc)  {
                            /* int showhextoo = 1; */
                            // print_exprloc_content(dbg, print_me, attrib, 1, lesb);

                            res = dwarf_formexprloc(attrib, &uval, &x, &podie_err);

                            if (res == DW_DLV_NO_ENTRY) {
                                /* Show nothing?  Impossible. */
                            } else if (res == DW_DLV_ERROR) {
                                print_error(dbg, "Cannot get a  DW_FORM_exprloc....", res, podie_err);
                            } else {
                                Dwarf_Half address_size = 0;
                                Dwarf_Half offset_size = 0;
                                Dwarf_Half version = 0;
                                int ares = 0;

                                ares = dwarf_get_version_of_die(print_me, &version, &offset_size);
                                if (ares != DW_DLV_OK) {
                                    print_error(dbg,"ERROR: Cannot get version size for exprloc die",
                                        DW_DLV_ERROR,podie_err);
                                }

                                ares = dwarf_get_die_address_size(print_me, &address_size, &podie_err);
                                
                                /*  Here res and not ares does not make sense but this is the original from dwarfdump   */
                                if (res == DW_DLV_NO_ENTRY) {
                                    print_error(dbg,"Cannot get die address size for exprloc", ares, podie_err);
                                } else if (res == DW_DLV_ERROR) {
                                    print_error(dbg,"Cannot Get die address size for exprloc", ares, podie_err);
                                } else {
                                    // get_string_from_locs(dbg, x, uval, address_size, 
                                    //     offset_size, version, esbp);

                                    // get_string_from_locs(Dwarf_Debug dbg,
                                    //     Dwarf_Ptr bytes_in,
                                    //     Dwarf_Unsigned block_len,
                                    //     Dwarf_Half addr_size,
                                    //     Dwarf_Half offset_size,
                                    //     Dwarf_Half version,
                                    //     char *out_string)

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
                                    Dwarf_Unsigned ulistlen = 0;
                                    
                                    res = dwarf_loclist_from_expr_c(dbg,
                                        x, uval,
                                        address_size,
                                        offset_size,
                                        version,
                                        &head,
                                        &ulistlen,
                                        &podie_err);

                                    if(res == DW_DLV_NO_ENTRY) {
                                        printf("getLocalVariablesAttributes: res == DW_DLV_NO_ENTRY\n");
                                        break;
                                    }

                                    if(res == DW_DLV_ERROR) {
                                        print_error(dbg, "dwarf_get_loclist_from_expr_c",
                                            res, podie_err);
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
                                        &podie_err);

                                    if (lres == DW_DLV_ERROR) {
                                        print_error(dbg, "dwarf_get_locdesc_entry_c", lres, podie_err);
                                    } else if (lres == DW_DLV_NO_ENTRY) {
                                        printf("getLocalVariablesAttributes: res == DW_DLV_NO_ENTRY\n");
                                        break;
                                    }

                                    Dwarf_Small op = 0;
                                    Dwarf_Unsigned opd1 = 0;
                                    Dwarf_Unsigned opd2 = 0;
                                    Dwarf_Unsigned opd3 = 0;
                                    Dwarf_Unsigned offsetforbranch = 0;

                                    for (int j = 0; j < ulocentry_count; j++) {
                                        // res = _dwarf_print_one_expr_op(dbg, NULL, locentry, j, 0, lesb2);

                                        /* DWARF 2,3,4 and DWARF5 style */
                                        res = dwarf_get_location_op_value_c(locentry,
                                            j, &op, &opd1, &opd2, &opd3, &offsetforbranch, &podie_err);

                                        switch (op) {
                                            case DW_OP_fbreg:
                                                // formx_signed(opd1,string_out);
                                                // printf("getLocalVariablesAttributes: opd1: 0x%llX, opd1: 0x%llu, opd1: 0x%lld\n", opd1, opd1, opd1);
                                                
                                                if (isLocalScope)
                                                {
                                                    variablesListTail->relativeMemoryLocation = opd1;
                                                }
                                                else
                                                {
                                                    printf("getLocalVariablesAttributes: Global scope but DW_OP_fbreg offset\n");

                                                    variablesListTail->memoryAddress = opd1;
                                                }

                                                break;
                                            case DW_OP_addr:
                                                if (isLocalScope)
                                                {
                                                    printf("getLocalVariablesAttributes: Non global scope but DW_OP_addr\n");

                                                    variablesListTail->relativeMemoryLocation = opd1;
                                                }
                                                else
                                                {
                                                    variablesListTail->memoryAddress = opd1;
                                                }

                                                break;    
                                            default:
                                                printf("getLocalVariablesAttributes: op is %c\n", op);

                                                break;
                                        }

                                        if (res != DW_DLV_OK) {
                                            print_error(dbg,
                                                "dwarf_get_location_op_value_c unexpected value!",
                                                DW_DLV_OK, podie_err);
                                        }
                                    }

                                    // printf("getLocalVariablesAttributes: section_offset: 0x%llX, locdesc_offset: 0x%llX, lesb22: %s\n", section_offset, locdesc_offset, lesb2);
                                }
                            }
                        } else {    
                            show_attr_form_error(dbg, attr, theform, lesb);
                        }

                        // printf("getLocalVariablesAttributes: DW_AT_location: %s, variablesListTail->relativeMemoryLocation: %d\n", lesb, variablesListTail->relativeMemoryLocation);
#ifdef PRINT_DEBUG_MESSAGES                        
                        if (isLocalScope)
                        {
                            printf("getLocalVariablesAttributes: DW_AT_location offset: %d\n", variablesListTail->relativeMemoryLocation);
                        }
                        else
                        {
                            printf("getLocalVariablesAttributes: DW_AT_location address: 0x%X\n", variablesListTail->memoryAddress);
                        }
#endif
                    }

                    break;                    
                default:
                    printf("getLocalVariablesAttributes: Skipped attribute: 0x%X\n", attr);

                    break;
            }
        }
        else
        { 
            print_error(dbg, "dwarf_whatattr entry missing", ares, podie_err);
        }
    }
}

static void
getVariableTypeAttributes(Dwarf_Debug dbg, Dwarf_Die print_me,
    Dwarf_Off dieprint_cu_goffset, int level, struct srcfilesdata *sf,
    Dwarf_Attribute *atlist, Dwarf_Signed atcnt, baseTypesList *baseTypeNode, int isPointer)
{
    Dwarf_Error podie_err = 0;
    Dwarf_Attribute attrib = 0;
    int tres = 0;
    int res = 0;
    Dwarf_Half tag = 0;
    Dwarf_Error paerr = 0;
    Dwarf_Unsigned uval = 0;

    if (isPointer)
    {
        esb_constructor(baseTypeNode->name);
        strcpy(baseTypeNode->name, "pointer");
    }

    for (int i = 0; i < atcnt; i++) 
    {
        Dwarf_Half attr;
        int ares;

        ares = dwarf_whatattr(atlist[i], &attr, &podie_err);

        attrib = atlist[i];

        if (ares == DW_DLV_OK) {
            switch (attr) 
            {
                case DW_AT_name:
                case DW_AT_GNU_template_name:
                    if (isPointer)
                    {
                        printf("getVariableTypeAttributes: Pointer with DW_AT_name\n");
                    }
                    
                    tres = dwarf_tag(print_me, &tag, &paerr);

                    if (tres == DW_DLV_ERROR) {
                        tag = 0;
                    } else if (tres == DW_DLV_NO_ENTRY) {
                        tag = 0;
                    } else {
                        /* ok */
                    }
                    
                    esb_constructor(baseTypeNode->name);
                    
                    get_attr_value(dbg, tag, print_me,
                        dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount,
                        baseTypeNode->name, show_form_used, verbose);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getVariableTypeAttributes: Type Name: %s\n", baseTypeNode->name);
#endif                    
                    break;
                case DW_AT_type:
                {
                    if (!isPointer)
                    {
                        printf("getVariableTypeAttributes: Base type with DW_AT_type\n");
                    }
                    
                    Dwarf_Off ref_goff = 0;

                    res = dwarf_global_formref(attrib, &ref_goff, &paerr);

                    baseTypeNode->pointerTypeGOffset = ref_goff;
#ifdef PRINT_DEBUG_MESSAGES                    
                    printf("getVariableTypeAttributes: Pointer Type GOFF: 0x%X\n", baseTypeNode->pointerTypeGOffset);
#endif
                    /*  Check the type of type  */
                    uint32_t pointerType = lookUpBaseTypeEncoding (baseTypesHead, baseTypeNode->pointerTypeGOffset);

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getVariableTypeAttributes: Pointer Type lookup: 0x%X\n", pointerType);
#endif
                    /*  Even if it is double **, isFloatingPoint will not be set  -- FIXME  */
                    if (pointerType == DW_ATE_float)
                    {
                        baseTypeNode->isFloatingPoint = 1;
#ifdef PRINT_DEBUG_MESSAGES
                        printf("getVariableTypeAttributes: Pointer points to floating point\n");
#endif                        
                    }
                }

                    break;

                case DW_AT_encoding:
                    if (isPointer)
                    {
                        printf("getVariableTypeAttributes: Pointer with DW_AT_encoding\n");
                    }
                    // esb_constructor(lesb);

                    // get_small_encoding_integer_and_name(dbg, attrib, &uval,
                    //     "DW_AT_encoding", lesb,
                    //     get_ATE_name, &paerr,
                    //     show_form_used);

                    // printf("getVariableTypeAttributes: DW_AT_encoding: %s, uval: 0x%llX\n", lesb, uval);

                    /*  Encodings can be found in dwarf.h   */
                    res = get_small_encoding_integer_and_name(dbg,
                        attrib,
                        &uval,
                        /* attrname */ (const char *) NULL,
                        /* err_string */ ( char *) NULL,
                        (encoding_type_func) 0,
                        &paerr, show_form_used);

                    baseTypeNode->encoding = uval;

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getVariableTypeAttributes: DW_AT_encoding: 0x%X\n", baseTypeNode->encoding);
#endif
                    if (uval == DW_ATE_float)
                    {
                        baseTypeNode->isFloatingPoint = 1;
                    }

                    break;
                case DW_AT_byte_size:
                    res = get_small_encoding_integer_and_name(dbg,
                        attrib,
                        &uval,
                        /* attrname */ (const char *) NULL,
                        /* err_string */ ( char *) NULL,
                        (encoding_type_func) 0,
                        &paerr, show_form_used);

                    baseTypeNode->byteSize = uval;

#ifdef PRINT_DEBUG_MESSAGES
                    printf("getVariableTypeAttributes: DW_AT_byte_size: 0x%X\n", baseTypeNode->byteSize);
#endif                    
                    break;
                default:
#ifdef PRINT_DEBUG_MESSAGES                
                    printf("getVariableTypeAttributes: Skipped attribute: 0x%X\n", attr);
#endif
                    break;
            }
        }
        else
        { 
            print_error(dbg, "dwarf_whatattr entry missing", ares, podie_err);
        }
    }
}

// static int
// isDeclaration(Dwarf_Debug dbg, Dwarf_Die print_me,
//     Dwarf_Attribute *atlist, Dwarf_Signed atcnt, int isLocalScope)
// {
//     Dwarf_Error podie_err = 0;
//     Dwarf_Attribute attrib = 0;
//     Dwarf_Error paerr = 0;
//     int isDeclarationValue = 0;
//     Dwarf_Half attr;
//     int res, ares;

//     for (int i = 0; i < atcnt; i++) 
//     {
//         ares = dwarf_whatattr(atlist[i], &attr, &podie_err);

//         attrib = atlist[i];

//         if (ares == DW_DLV_OK) {
//             switch (attr) 
//             {
//                 case DW_AT_declaration:
//                 {
//                     Dwarf_Half theform = 0;
//                     // esb_constructor(lesb);
                    
//                     // get_attr_value(dbg, tag, print_me,
//                     //     dieprint_cu_goffset,attrib, sf->srcfiles, sf->srcfilescount,
//                     //     lesb, show_form_used, verbose);
//                     res = dwarf_whatform(attrib, &theform, &paerr);

//                     /*  Depending on the form and the attribute, process the form. */
//                     if (res == DW_DLV_ERROR) 
//                     {
//                         print_error(dbg, "dwarf_whatform cannot Find Attr Form", res, paerr);
//                     } 
//                     else if (res == DW_DLV_NO_ENTRY) 
//                     {
//                         printf("isDeclaration: DW_AT_declaration: DW_DLV_NO_ENTRY\n");
//                     }

//                     if (theform == DW_FORM_flag_present)
//                     {
//                         isDeclarationValue = 1;
                        
//                         if (isLocalScope)
//                         {
//                             printf("getLocalVariablesAttributes: Non global scope but DW_AT_declaration 1\n");   
//                         }
// #ifdef PRINT_DEBUG_MESSAGES
//                         printf("getLocalVariablesAttributes: DW_AT_declaration: 1\n");   
// #endif                        
//                     }
//                     else
//                     {
//                         printf("getLocalVariablesAttributes: Unknown theform: 0x%X\n", theform);
//                     }
//                 }
//                     break;
//                 case DW_AT_name:
//                 case DW_AT_GNU_template_name:
//                 case DW_AT_type:
//                 case DW_AT_decl_column:
//                 case DW_AT_decl_file:
//                 case DW_AT_decl_line:
//                 case DW_AT_external:
//                 case DW_AT_location:
//                 case DW_AT_frame_base:
//                     break;                    
//                 default:

//                     break;
//             }
//         }
//         else
//         { 
//             print_error(dbg, "dwarf_whatattr entry missing", ares, podie_err);
//         }
//     }

//     return isDeclarationValue;
// }

void
parseCompilationUnit(Dwarf_Debug dbg, Dwarf_Die print_me, Dwarf_Off overall_offset,
    Dwarf_Half tag, Dwarf_Attribute *atlist, Dwarf_Signed atcnt,
    Dwarf_Off dieprint_cu_goffset, int level, struct srcfilesdata *sf)
{
    static scopeType currentScope = kNoScope;

    /*  Create data stractures  */
    switch (tag)
    {
        case DW_TAG_compile_unit:
            if (compilationUnitsHead == NULL)
            {
                compilationUnitsHead = (compilationUnitList *) malloc(sizeof(compilationUnitList));

                compilationUnitsTail = compilationUnitsHead;
            }
            else
            {
                compilationUnitsTail->next = (compilationUnitList *) malloc(sizeof(compilationUnitList));

                compilationUnitsTail = compilationUnitsTail->next;
            }
            
            compilationUnitsTail->globalVariablesHead = NULL;
            compilationUnitsTail->globalVariablesTail = NULL;
            compilationUnitsTail->next = NULL;

            currentScope = kCompileUnitScope;

            getCompilationUnitAttributes(dbg, print_me, dieprint_cu_goffset, level, sf, atlist, atcnt);

            break;
        case DW_TAG_base_type:
            if (baseTypesHead == NULL)
            {
                baseTypesHead = (baseTypesList *) malloc(sizeof(baseTypesList));

                baseTypesTail = baseTypesHead;
            }
            else
            {
                baseTypesTail->next = (baseTypesList *) malloc(sizeof(baseTypesList));

                baseTypesTail = baseTypesTail->next;
            }
            
            baseTypesTail->isPointer = 0;
            baseTypesTail->isFloatingPoint = 0;
            baseTypesTail->globalOffset = overall_offset;
            baseTypesTail->compilationUnit = compilationUnitsTail;
            baseTypesTail->next = NULL;

            getVariableTypeAttributes(dbg, print_me, dieprint_cu_goffset, level, sf, atlist, atcnt, 
                baseTypesTail, baseTypesTail->isPointer);

            break;
        case DW_TAG_variable:
            
            if (currentScope == kCompileUnitScope)
            {
                if (compilationUnitsTail->globalVariablesHead == NULL)
                {
                    compilationUnitsTail->globalVariablesHead = (variablesList *) malloc(sizeof(variablesList));

                    compilationUnitsTail->globalVariablesTail = compilationUnitsTail->globalVariablesHead;
                }
                else
                {
                    compilationUnitsTail->globalVariablesTail->next = (variablesList *) malloc(sizeof(variablesList));

                    compilationUnitsTail->globalVariablesTail = compilationUnitsTail->globalVariablesTail->next;
                }
                
                compilationUnitsTail->globalVariablesTail->isPointer = 0;
                compilationUnitsTail->globalVariablesTail->isTraced = 0;
                compilationUnitsTail->globalVariablesTail->isFloatingPoint = 0;
                compilationUnitsTail->globalVariablesTail->isExternal = 0;
                compilationUnitsTail->globalVariablesTail->typeGlobalOffset = 0x00;
                compilationUnitsTail->globalVariablesTail->compilationUnit = compilationUnitsTail;
                compilationUnitsTail->globalVariablesTail->next = NULL;

                getLocalVariablesAttributes(dbg, print_me, dieprint_cu_goffset, level, sf, atlist, atcnt, compilationUnitsTail->globalVariablesTail, 0);
            }
            else if (currentScope == kSubProgramScope)
            {
                if (subProgramsTail->localVariablesHead == NULL)
                {
                    subProgramsTail->localVariablesHead = (variablesList *) malloc(sizeof(variablesList));

                    subProgramsTail->localVariablesTail = subProgramsTail->localVariablesHead;
                }
                else
                {
                    subProgramsTail->localVariablesTail->next = (variablesList *) malloc(sizeof(variablesList));

                    subProgramsTail->localVariablesTail = subProgramsTail->localVariablesTail->next;
                }
                
                subProgramsTail->localVariablesTail->isPointer = 0;
                subProgramsTail->localVariablesTail->isTraced = 0;
                subProgramsTail->localVariablesTail->isFloatingPoint = 0;
                subProgramsTail->localVariablesTail->isExternal = 0;
                subProgramsTail->localVariablesTail->typeGlobalOffset = 0x00;
                subProgramsTail->localVariablesTail->compilationUnit = compilationUnitsTail;
                subProgramsTail->localVariablesTail->next = NULL;

                getLocalVariablesAttributes(dbg, print_me, dieprint_cu_goffset, level, sf, atlist, atcnt, subProgramsTail->localVariablesTail, 1);
            }
            else if (currentScope == kSubRoutineScope)
            {
                // static int
                // isDeclaration(Dwarf_Debug dbg, Dwarf_Die print_me,
                //     Dwarf_Attribute *atlist, Dwarf_Signed atcnt, int isLocalScope)
                                
                printf("DW_TAG_variable in kSubRoutineScope\n");
            }
            else
            {
                printf("Weird scope: %d in DW_TAG_variable\n", currentScope);
            }
            
            break;
        case DW_TAG_subprogram:
            currentScope = kSubProgramScope;

            if (subProgramsHead == NULL)
            {
                subProgramsHead = (subProgramsList *) malloc(sizeof(subProgramsList));

                subProgramsTail = subProgramsHead;
            }
            else
            {
                subProgramsTail->next = (subProgramsList *) malloc(sizeof(subProgramsList));

                subProgramsTail = subProgramsTail->next;
            }
            
            subProgramsTail->formalParametersHead = NULL;
            subProgramsTail->formalParametersTail = NULL;
            subProgramsTail->localVariablesHead = NULL;
            subProgramsTail->localVariablesTail = NULL;
            subProgramsTail->isPointer = 0;
            subProgramsTail->isFloatingPoint = 0;
            subProgramsTail->typeGlobalOffset = 0x0;
            subProgramsTail->compilationUnit = compilationUnitsTail;
            subProgramsTail->next = NULL;

            getSubProgramAttributes(dbg, print_me, dieprint_cu_goffset, level, sf, atlist, atcnt); 

            break;
        case DW_TAG_formal_parameter:
            if (currentScope == kSubProgramScope)
            {
                if (subProgramsTail->formalParametersHead == NULL)
                {
                    subProgramsTail->formalParametersHead = (variablesList *) malloc(sizeof(variablesList));

                    subProgramsTail->formalParametersTail = subProgramsTail->formalParametersHead;
                }
                else
                {
                    subProgramsTail->formalParametersTail->next = (variablesList *) malloc(sizeof(variablesList));

                    subProgramsTail->formalParametersTail = subProgramsTail->formalParametersTail->next;
                }
                
                subProgramsTail->formalParametersTail->isPointer = 0;
                subProgramsTail->formalParametersTail->isTraced = 0;
                subProgramsTail->formalParametersTail->isFloatingPoint = 0;
                subProgramsTail->formalParametersTail->isExternal = 0;
                subProgramsTail->formalParametersTail->typeGlobalOffset = 0x00;
                subProgramsTail->formalParametersTail->compilationUnit = compilationUnitsTail;
                subProgramsTail->formalParametersTail->next = NULL;

                getLocalVariablesAttributes(dbg, print_me, dieprint_cu_goffset, level, sf, atlist, atcnt, subProgramsTail->formalParametersTail, 1);
            }
            else if (currentScope == kCompileUnitScope)
            {
                /*  Formal parameters belonging to a subroutine type (i.e., function pointer)    */
                /*  DWARF Debugging Information Format Version 4 June 10, 2010 - Section 5.8 Subroutine Type Entries - page 97   */
                /*  It is possible in C to declare pointers to subroutines that return a value of a specific type */
            }
            else if (currentScope == kSubRoutineScope)
            {
                /*  Skip for now    */
            }
            else
            {
                printf("Weird scope: %d in DW_TAG_formal_parameter\n", currentScope);
            }

            break;
        case DW_TAG_pointer_type:
            if (baseTypesHead == NULL)
            {
                baseTypesHead = (baseTypesList *) malloc(sizeof(baseTypesList));

                baseTypesTail = baseTypesHead;
            }
            else
            {
                baseTypesTail->next = (baseTypesList *) malloc(sizeof(baseTypesList));

                baseTypesTail = baseTypesTail->next;
            }
            
            baseTypesTail->isPointer = 1;
            baseTypesTail->isFloatingPoint = 0;
            baseTypesTail->globalOffset = overall_offset;
            baseTypesTail->compilationUnit = compilationUnitsTail;
            baseTypesTail->next = NULL;

            getVariableTypeAttributes(dbg, print_me, dieprint_cu_goffset, level, sf, atlist, atcnt, 
                baseTypesTail, baseTypesTail->isPointer);

            break;
        case DW_TAG_array_type:
            /*  Consider DW_TAG_array_type as a DW_TAG_pointer_type with byteSize 0x00 */
            if (baseTypesHead == NULL)
            {
                baseTypesHead = (baseTypesList *) malloc(sizeof(baseTypesList));

                baseTypesTail = baseTypesHead;
            }
            else
            {
                baseTypesTail->next = (baseTypesList *) malloc(sizeof(baseTypesList));

                baseTypesTail = baseTypesTail->next;
            }
            
            baseTypesTail->isPointer = 1;
            baseTypesTail->isFloatingPoint = 0;
            baseTypesTail->byteSize = 0;
            baseTypesTail->globalOffset = overall_offset;
            baseTypesTail->compilationUnit = compilationUnitsTail;
            baseTypesTail->next = NULL;

            getVariableTypeAttributes(dbg, print_me, dieprint_cu_goffset, level, sf, atlist, atcnt, 
                baseTypesTail, baseTypesTail->isPointer);

            break;
        case DW_TAG_subroutine_type:
            /*  Add to some types list? -- FIXME    */
            // currentScope = kSubRoutineScope;

            break;
        case DW_TAG_subrange_type:
        case DW_TAG_lexical_block:
        /*  DW_TAG_const_type   */
        /*  DW_TAG_structure_type   */
        /*  DW_TAG_member   */
        /*  DW_TAG_typedef  */
        /*  DW_TAG_enumeration_type */
        /*  DW_TAG_enumerator   */
        default:
            break;
    }
}

void
printDwarfTracingDataStructures(void)
{
    compilationUnitList *oneCompilationUnit;
    variablesList *oneVariable;
    subProgramsList *oneSubProgram;

    for (oneCompilationUnit = compilationUnitsHead; oneCompilationUnit != NULL; oneCompilationUnit = oneCompilationUnit->next)
    {
        printf("\n----Compilation unit %s----\n", oneCompilationUnit->name);

        printf("Global scope variables:\n");

        for (oneVariable = oneCompilationUnit->globalVariablesHead; oneVariable != NULL; oneVariable = oneVariable->next)
        {
            getTypeForVariable(baseTypesHead, oneVariable, oneVariable->typeGlobalOffset);
        
            printf("Variable: %s\tisPointer: %d\tisFloatingPoint: %d", 
                oneVariable->name, oneVariable->isPointer, oneVariable->isFloatingPoint);

            printf("\ttypeGlobalOffset: 0x%X\tisExternal: %d\tisTraced: %d\tmemoryAddress: 0x%X\n", 
                oneVariable->typeGlobalOffset, oneVariable->isExternal, oneVariable->isTraced, oneVariable->memoryAddress);                
        }

        printf("\nSubprograms:\n");

        for (oneSubProgram = subProgramsHead; oneSubProgram != NULL; oneSubProgram = oneSubProgram->next)
        {
            if (oneSubProgram->compilationUnit == oneCompilationUnit)
            {
                getTypeForSubProgram(baseTypesHead, oneSubProgram, oneSubProgram->typeGlobalOffset);
                
                printf("\nSubprogram: %s\t\tisPointer: %d\tisFloatingPoint: %d", 
                    oneSubProgram->name, oneSubProgram->isPointer, oneSubProgram->isFloatingPoint);

                printf("\ttypeGlobalOffset: 0x%X\tlowPC: 0x%X\thighPC: 0x%X\n", 
                    oneSubProgram->typeGlobalOffset, oneSubProgram->lowPC, oneSubProgram->highPC);                    

                for (oneVariable = oneSubProgram->formalParametersHead; oneVariable != NULL; oneVariable = oneVariable->next)
                {
                    getTypeForVariable(baseTypesHead, oneVariable, oneVariable->typeGlobalOffset);

                    printf("For-Param: %s\tisPointer: %d\tisFloatingPoint: %d", 
                        oneVariable->name, oneVariable->isPointer, oneVariable->isFloatingPoint);

                    printf("\ttypeGlobalOffset: 0x%X\tisExternal: %d\tisTraced: %d\trelativeMemoryLocation: %d\n", 
                        oneVariable->typeGlobalOffset, oneVariable->isExternal, oneVariable->isTraced, oneVariable->relativeMemoryLocation);
                }

                for (oneVariable = oneSubProgram->localVariablesHead; oneVariable != NULL; oneVariable = oneVariable->next)
                {
                    getTypeForVariable(baseTypesHead, oneVariable, oneVariable->typeGlobalOffset);

                    printf("Local-var: %s\tisPointer: %d\tisFloatingPoint: %d", 
                        oneVariable->name, oneVariable->isPointer, oneVariable->isFloatingPoint);

                    printf("\ttypeGlobalOffset: 0x%X\tisExternal: %d\tisTraced: %d\trelativeMemoryLocation: %d\n", 
                        oneVariable->typeGlobalOffset, oneVariable->isExternal, oneVariable->isTraced, oneVariable->relativeMemoryLocation);
                }
            }
        }
    }
}

int
cuAllowedForParsing(uint32_t cuGOffset)
{
    int offsetAllowed = 0;
    firstParseCUsList   *oneAllowedOffsetNode;
    
    oneAllowedOffsetNode = firstParseCUsHead;

    /*  Check if current line belongs to the loaded libs    */
    while ((!offsetAllowed) && (oneAllowedOffsetNode != NULL))
    {
        if (oneAllowedOffsetNode->cuGOffset == cuGOffset)
        {
            offsetAllowed = 1;
        }

        oneAllowedOffsetNode = oneAllowedOffsetNode->next;
    }

    return offsetAllowed;
}

int
getNumberOfUserCUsFromMapfile(char *filename)
{
	FILE	        *fp;
	char	        line[ESB_S_CHAR_LENGTH], previousLib[ESB_S_CHAR_LENGTH], *p, *debugInfoLib;
	int		        nlines = 0;
	char 	        dataSegmentStr[9];
    linkedLibsList  *linkedLibsHead=NULL, *linkedLibsTail, *oneLinkedLib;
    uint32_t        debugInfoAddress;
    int	            i = 0;
    int             libFound = 0;


	if ((fp = fopen(filename, "r")) == NULL)
	{
		// mprint(E, S, nodeinfo,
		printf("Open of \"%s\" failed...\n\n", filename);
		return 0;
	}
	else
	{
		// mprint(E, S, nodeinfo,
		printf("Loading \"%s\" map file...\n", filename);
	}
	
    // fscanf(fp, "%s\n", line);
    fgets(line, sizeof(line), fp);

    if (strcmp(line, "Archive member included to satisfy reference by file (symbol)\n"))
    {
        printf("load_mapfile: First line of map file: %s\n", line);

        return 0;
    }

    esb_constructor(previousLib);

    /*  Skip line   */
    // fscanf(fp, "%*s\n");
    fgets(line, sizeof(line), fp);
    
    /*  Pairs like  */
    /*  /home/billtsou/Desktop/UPP/signaloid-sunflower/tools/tools-lib/riscv//libm.a(lib_a-s_atan.o) */
    /*                            UPP_SpeedCalcGPS.o (atan) */
    fscanf(fp, "%s\n", line);

    // printf("load_mapfile: readStrLen: %ld: line: %s\n", strlen(line), line);

    while (strlen(line) > 1)
    {
        p = strtok(line, "(");

        // printf("One lib name: %s\n", p);

        /*  Libs areas repeatedly but in consequtive apperance  */
        if (strcmp(p, previousLib))
        {
            if (linkedLibsHead == NULL)
            {
                linkedLibsHead = (linkedLibsList *) malloc(sizeof(linkedLibsList));

                linkedLibsTail = linkedLibsHead;
            }
            else
            {
                linkedLibsTail->next = (linkedLibsList *) malloc(sizeof(linkedLibsList));

                linkedLibsTail = linkedLibsTail->next;
            }
            
            esb_constructor(linkedLibsTail->name);
            
            strcpy(linkedLibsTail->name, p);

            strcpy(previousLib, p);
            
            linkedLibsTail->next = NULL;
        }

        /*  Skip line   */
        fgets(line, sizeof(line), fp);

        // fscanf(fp, "%s\n", line);
        fgets(line, sizeof(line), fp);

        // printf("load_mapfile: New line len: %ld: line: %s\n", strlen(line), line);
    }

    printf("\nLoads archive libs\n");

    for (oneLinkedLib=linkedLibsHead; oneLinkedLib!=NULL; oneLinkedLib=oneLinkedLib->next)
    {
        printf("%s\n", oneLinkedLib->name);
    }

	/*														*/
	/*		Skip all lines until the DATA_SEGMENT_END		*/
	/*														*/
	for (; strstr(line, "DATA_SEGMENT_END") == NULL ; nlines++)
	{
		fgets(line, sizeof(line), fp);
	}

	p = strtok(line, " \t");

	/*	18 is for 64bit addresses and 10 for 32bit addresses	*/
	if (strlen(p) == 18)
	{
		strcpy(dataSegmentStr, &p[10]);
	}
	else if (strlen(p) == 10)
	{
		strcpy(dataSegmentStr, &p[2]);
	}
	else
	{
		printf("Unknown memory length %ld in mmap file.\n", strlen(p));
		return 0;
	}
	
    /*														*/
	/*		Skip all lines until the first  .debug_info		*/
	/*														*/
	for (; strstr(line, " .debug_info") == NULL ; nlines++)
	{
		fgets(line, sizeof(line), fp);
	}

    /*  Example line: .debug_info    0x000000000000133c      0xb86 /home/billtsou/Desktop/UPP/signaloid-sunflower/tools/tools-lib/riscv//libm.a(lib_a-s_atan.o) */
    while (strlen(line) > 1)
    {
        i = 0;

        libFound = 0;

        debugInfoLib = NULL;

        for ((p = strtok(line, " \n\t")); p; (p = strtok(NULL, " \n\t")), i++)
        {
            // printf("Token: %s\n", p);
            if (i == 1)
            {
                debugInfoAddress = strtol(p, NULL, 16);
            }
            else if (i == 3)
            {
                debugInfoLib = strtok(p, "(");
            }
        }

        // printf("debugInfoAddress: 0x%X debugInfoLib: %s\n", debugInfoAddress, debugInfoLib);

        oneLinkedLib = linkedLibsHead;

        /*  Check if current line belongs to the loaded libs    */
        while ((!libFound) && (oneLinkedLib != NULL))
        {
            if (!strcmp(oneLinkedLib->name, debugInfoLib))
            {
                libFound = 1;
            }

            oneLinkedLib = oneLinkedLib->next;
        }

        /*  Current line does not belong to the loaded libs    */
        if (!libFound)
        {
            printf("CU with debugInfoAddress: 0x%X debugInfoLib: %s will be processed\n", debugInfoAddress, debugInfoLib);

            if (firstParseCUsHead == NULL)
            {
                firstParseCUsHead = (firstParseCUsList *) malloc(sizeof(firstParseCUsList));

                firstParseCUsTail = firstParseCUsHead;
            }
            else
            {
                firstParseCUsTail->next = (firstParseCUsList *) malloc(sizeof(firstParseCUsList));

                firstParseCUsTail = firstParseCUsTail->next;
            }
            
            firstParseCUsTail->cuGOffset = debugInfoAddress;
            
            firstParseCUsTail->next = NULL;
        }

        fgets(line, sizeof(line), fp);
    }

    /*  Cleanup */
    while(linkedLibsHead!=NULL)
    {
        oneLinkedLib=linkedLibsHead;
        
        linkedLibsHead=linkedLibsHead->next;

        free(oneLinkedLib);
    }

	fclose(fp);

    return 0;
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
    Dwarf_Error *errp  = 0;
    
    if(argc < 2) {
        fd = 0; /* stdin */
    } else {
        filepath = argv[1];
        
        fd = open(filepath, O_RDONLY);
    
        if(fd < 0)
        {
            printf("Failure attempting to open \"%s\"\n", filepath);
        }

        errp = &error;
    }    

    getNumberOfUserCUsFromMapfile(argv[2]);

    // return 0;

    intGlFlags();

    res = dwarf_init(fd, DW_DLC_READ, errhand, errarg, &dbg, errp);
    
    if(res != DW_DLV_OK) 
    {
        printf("Giving up, cannot do DWARF processing\n");
        exit(1);
    }

    read_cu_list(dbg, TRUE);

    printDwarfTracingDataStructures();

    res = dwarf_finish(dbg, errp);
    
    if(res != DW_DLV_OK) {
        printf("dwarf_finish failed!\n");
    }

    /*  FIXME -- Cleanup    */

    close(fd);

    return 0;
}

