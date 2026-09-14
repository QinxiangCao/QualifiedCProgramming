/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko

#include "solver_qcp.h"

#include <stdio.h>
#include <stdlib.h>

//=================================================================================================
// Helpers:


// Reads an input stream to end-of-file and returns the result as a 'char*' terminated by '\0'
// (dynamic allocation in case 'in' is standard input).
// Native allocation failure in this helper remains intentionally unchecked and deferred.
//
char* readFile(FILE *  in)
{
    char*   data = malloc(65536);
    int     cap  = 65536;
    int     size = 0;

    while (!feof(in)){
        if (size == cap){
            cap *= 2;
            data = realloc(data, cap); }
        size += fread(&data[size], 1, 65536, in);
    }
    data = realloc(data, size+1);
    data[size] = '\0';

    return data;
}


//=================================================================================================
// DIMACS Parser:


static inline void skipWhitespace(char** in) {
    while ((**in >= 9 && **in <= 13) || **in == 32)
        (*in)++; }

static inline void skipLine(char** in) {
    for (;;){
        if (**in == 0) return;
        if (**in == '\n') { (*in)++; return; }
        (*in)++; } }

static inline int parseInt(char** in) {
    int     val = 0;
    int    _neg = 0;
    skipWhitespace(in);
    if      (**in == '-') _neg = 1, (*in)++;
    else if (**in == '+') (*in)++;
    if (**in < '0' || **in > '9') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", **in), exit(1);
    while (**in >= '0' && **in <= '9')
        val = val*10 + (**in - '0'),
        (*in)++;
    return _neg ? -val : val; }

static int readClause(char** in, veci* lits) {
    int parsed_lit, var;
    int status;

    veci_resize(lits,0);
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        status = veci_push(lits, (parsed_lit > 0 ? toLit(var) : lit_neg(toLit(var))));
        if (status == MINISAT_CAPACITY_EXHAUSTED)
            return MINISAT_CAPACITY_EXHAUSTED;
    }
    return 1;
}

static int parse_DIMACS_main(char* in, solver* s) {
    veci lits;
    int status;

    veci_new(&lits);

    for (;;){
        skipWhitespace(&in);
        if (*in == 0)
            break;
        else if (*in == 'c' || *in == 'p')
            skipLine(&in);
        else{
            lit* begin;
            status = readClause(&in, &lits);
            if (status == MINISAT_CAPACITY_EXHAUSTED) {
                veci_delete(&lits);
                return MINISAT_CAPACITY_EXHAUSTED;
            }
            begin = veci_begin(&lits);
            status = solver_addclause(s, begin, begin+veci_size(&lits));
            if (status == MINISAT_CAPACITY_EXHAUSTED) {
                veci_delete(&lits);
                return MINISAT_CAPACITY_EXHAUSTED;
            }
            if (status == 0) {
                veci_delete(&lits);
                return 0;
            }
        }
    }
    veci_delete(&lits);

    status = solver_simplify(s);
    if (status == MINISAT_CAPACITY_EXHAUSTED)
        return MINISAT_CAPACITY_EXHAUSTED;
    if (status == 0)
        return 0;
    return 1;
}


// Inserts problem into solver. Returns 0 upon immediate conflict and -2 upon capacity exhaustion.
//
static int parse_DIMACS(FILE * in, solver* s) {
    char* text = readFile(in);
    int ret = parse_DIMACS_main(text, s);
    free(text);
    return ret; }


//=================================================================================================


int main(int argc, char** argv)
{
    solver* s = solver_new();
    int     status;
    FILE *  in;

    if (argc != 2)
        fprintf(stderr, "ERROR! Not enough command line arguments.\n"),
        exit(1);

    in = fopen(argv[1], "rb");
    if (in == NULL)
        fprintf(stderr, "ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]),
        exit(1);
    status = parse_DIMACS(in, s);
    fclose(in);

    if (status == MINISAT_CAPACITY_EXHAUSTED) {
        solver_delete(s);
        fprintf(stderr, "MINISAT_CAPACITY_EXHAUSTED\n");
        return 2;
    }
    if (status == 0) {
        solver_delete(s);
        printf("UNSATISFIABLE\n");
        return 20;
    }

    status = solver_solve(s,0,0);
    if (status == MINISAT_CAPACITY_EXHAUSTED) {
        solver_delete(s);
        fprintf(stderr, "MINISAT_CAPACITY_EXHAUSTED\n");
        return 2;
    }
    if (status == 0) {
        solver_delete(s);
        printf("UNSATISFIABLE\n");
        return 20;
    }
    /* status == 1 is the only SAT path after solver_solve. */
    printf("SATISFIABLE\n");
    solver_delete(s);
    return 10;
}
