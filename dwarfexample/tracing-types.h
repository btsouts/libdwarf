#include <stdint.h>

#define COMPILATION_UNIT_STR_LEN 1024

/*	XXX */
typedef struct compilationUnitList compilationUnitList;

typedef struct variablesList variablesList;

struct compilationUnitList
{
	char					name[COMPILATION_UNIT_STR_LEN];
	char					compDir[COMPILATION_UNIT_STR_LEN];
	uint32_t                lowPC;
    uint32_t                highPC;
    
    /*  Pointer to subprograms? */
    variablesList           *globalVariablesHead, *globalVariablesTail;
    compilationUnitList		*next;
};

// typedef struct globalVariablesList globalVariablesList;

// /*  DW_AT_external?  */
// struct globalVariablesList
// {
// 	char					name[COMPILATION_UNIT_STR_LEN];
//     int                     isPointer;
//     int                     isTraced;
//     int                     isDouble;
//     uint32_t                memoryAddress;
//     /*  DW_AT_decl_file */
//     /*  DW_AT_decl_line */
//     /*  DW_AT_decl_column   */
//     compilationUnitList     *compilationUnit;    
//     globalVariablesList		*next;
// };

// typedef struct formalParametersList formalParametersList;

// struct formalParametersList
// {
// 	char					name[COMPILATION_UNIT_STR_LEN];
//     int                     isPointer;
//     int                     isTraced;
//     int                     isDouble;
//     uint32_t                relativeMemoryLocation;
//     /*  DW_AT_decl_file */
//     /*  DW_AT_decl_line */
//     /*  DW_AT_decl_column */
//     compilationUnitList     *compilationUnit;    
//     formalParametersList	*next;
// };

/* *argv[] -> pointer to pointer 
 * *argv[15] -> pointer to pointer
 * double srcA[128] -> pointer
 */

struct variablesList
{
	char					name[COMPILATION_UNIT_STR_LEN];
    int                     isPointer;
    int                     isTraced;
    int                     isFloatingPoint;
    int                     isExternal;
    uint32_t                typeGlobalOffset;
    
    union { /* Maybe it needs a 64 bit data types  */
        uint32_t            memoryAddress;    
        int                 relativeMemoryLocation; 
    };

    /*  DW_AT_decl_file */
    /*  DW_AT_decl_line */
    /*  DW_AT_decl_column */
    compilationUnitList     *compilationUnit;    
    variablesList	        *next;
};

typedef struct baseTypesList baseTypesList;

struct baseTypesList
{
	char					name[COMPILATION_UNIT_STR_LEN];
    int                     isPointer;
    int                     isFloatingPoint;
    uint32_t                globalOffset;
    uint32_t                byteSize;
    
    union { 
        uint32_t            encoding;    
        uint32_t            pointerTypeGOffset; /* Maybe it needs a 64 bit data types  */
    };

    compilationUnitList     *compilationUnit;    
    baseTypesList	        *next;
};

typedef struct subProgramsList subProgramsList;

struct subProgramsList
{
	char					name[COMPILATION_UNIT_STR_LEN];
    int                     isPointer;
    int                     isFloatingPoint;
    uint32_t                typeGlobalOffset;
    uint32_t                lowPC;
    uint32_t                highPC;
    /*  DW_AT_decl_file */
    /*  DW_AT_decl_line */
    /*  DW_AT_decl_column   */
    compilationUnitList     *compilationUnit;
    variablesList           *formalParametersHead, *formalParametersTail;
    variablesList           *localVariablesHead, *localVariablesTail;
    subProgramsList		    *next;
};

typedef enum
{
	kNoScope,
    kCompileUnitScope,
	kSubProgramScope,
	kSubRoutineScope,
	kScopeMax,
} scopeType;


