#include <stdint.h>

#define COMPILATION_UNIT_STR_LEN 1024

/*	XXX */
typedef struct compilationUnitList compilationUnitList;

struct compilationUnitList
{
	char					name[COMPILATION_UNIT_STR_LEN];
	char					compDir[COMPILATION_UNIT_STR_LEN];
	uint32_t                lowPC;
    uint32_t                highPC;
    /*  Pointer to subprograms? */
    /*  Pointer to global variable ?    */
    compilationUnitList		*next;
};

typedef struct globalVariablesList globalVariablesList;

/*  DW_AT_external?  */
struct globalVariablesList
{
	char					name[COMPILATION_UNIT_STR_LEN];
    int                     isPointer;
    int                     isTraced;
    int                     isDouble;
    uint32_t                memoryAddress;
    /*  DW_AT_decl_file */
    /*  DW_AT_decl_line */
    /*  DW_AT_decl_column   */
    compilationUnitList     *compilationUnit;    
    globalVariablesList		*next;
};

typedef struct formalParametersList formalParametersList;

struct formalParametersList
{
	char					name[COMPILATION_UNIT_STR_LEN];
    int                     isPointer;
    int                     isTraced;
    int                     isDouble;
    uint32_t                relativeMemoryLocation;
    /*  DW_AT_decl_file */
    /*  DW_AT_decl_line */
    /*  DW_AT_decl_column */
    compilationUnitList     *compilationUnit;    
    formalParametersList	*next;
};

typedef struct localVariablesList localVariablesList;

struct localVariablesList
{
	char					name[COMPILATION_UNIT_STR_LEN];
    int                     isPointer;
    int                     isTraced;
    int                     isDouble;
    uint32_t                relativeMemoryLocation;
    /*  DW_AT_decl_file */
    /*  DW_AT_decl_line */
    /*  DW_AT_decl_column */
    compilationUnitList     *compilationUnit;    
    localVariablesList	    *next;
};

typedef struct baseTypesList baseTypesList;

struct baseTypesList
{
	char					name[COMPILATION_UNIT_STR_LEN];
    int                     isPointer;
    int                     isDouble;
    uint32_t                globalOffset;
    compilationUnitList     *compilationUnit;    
    baseTypesList	        *next;
};

typedef struct subProgramsList subProgramsList;

struct subProgramsList
{
	char					name[COMPILATION_UNIT_STR_LEN];
    int                     isPointer;
    int                     isDouble;
    uint32_t                lowPC;
    uint32_t                highPC;
    /*  DW_AT_decl_file */
    /*  DW_AT_decl_line */
    /*  DW_AT_decl_column   */
    compilationUnitList     *compilationUnit;
    formalParametersList    *formalParametersHead, *formalParametersTail;
    localVariablesList      *localVariablesHead, *localVariablesTail;
    subProgramsList		    *next;
};