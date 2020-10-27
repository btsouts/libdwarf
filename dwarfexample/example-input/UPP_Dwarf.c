#include <uncertain.h>
#include <printf.h>

#define NUMBER_OF_SAMPLES 32

double
additionSubProgram(double srcA, double srcB)
{
	double result;

	result = srcA + srcB;

	return result;
}

int 
main(int argc, char *argv[])
{
	/* Test with floating point values */
	double doubleSamples[NUMBER_OF_SAMPLES];

	double uncertainDoubleVariableA=0.0, uncertainDoubleVariableB=0.0, uncertainDoubleVariableC=0.0;

	uncertainDoubleVariableA = 1.0;

	uncertainDoubleVariableB = 2.5; 

	uncertainDoubleVariableC = additionSubProgram(uncertainDoubleVariableA, uncertainDoubleVariableB);

	printf("uncertainDoubleVariableC: %f\n", uncertainDoubleVariableC);

	return 0;
}

