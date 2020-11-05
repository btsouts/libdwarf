/*
	Authored 2020, Vasileios Tsoutsouras and Phillip Stanley-Marbell.

	All rights reserved.

	Redistribution and use in source and binary forms, with or without
	modification, are permitted provided that the following conditions
	are met:

	*	Redistributions of source code must retain the above
		copyright notice, this list of conditions and the following
		disclaimer.

	*	Redistributions in binary form must reproduce the above
		copyright notice, this list of conditions and the following
		disclaimer in the documentation and/or other materials
		provided with the distribution.

	*	Neither the name of the author nor the names of its
		contributors may be used to endorse or promote products
		derived from this software without specific prior written
		permission.

	THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
	"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
	LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
	FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
	COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
	INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
	BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
	LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
	CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
	LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
	ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
	POSSIBILITY OF SUCH DAMAGE.
*/
#ifndef _DWARF_TRACING_TYPES_H
#define _DWARF_TRACING_TYPES_H

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
	kSubRoutineScope, /* Should remove this */
	kScopeMax,
} scopeType;

#endif
