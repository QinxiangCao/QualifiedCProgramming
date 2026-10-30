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
#include <time.h>

//=================================================================================================
// Helpers:


// Reads an input stream to end-of-file and returns the result as a 'char*' terminated by '\0'
// (dynamic allocation in case 'in' is standard input).
//
char* readFile(FILE *in)
{
    size_t cap = 65536;
    size_t size = 0;
    char *data = vec_checked_alloc(cap, 1, 0);

    for (;;) {
        size_t count;
        if (size == cap - 1) {
            size_t required, preferred;
            char *next = NULL;
            if (cap == SIZE_MAX)
                vec_resource_stop();
            required = cap + 1;
            preferred = cap <= SIZE_MAX / 2 ? cap * 2 : required;
            next = realloc(data, preferred);
            if (next == NULL && required < preferred) {
                preferred = required;
                next = realloc(data, preferred);
            }
            if (next == NULL)
                vec_resource_stop();
            data = next;
            cap = preferred;
        }
        count = fread(data + size, 1, cap - size - 1, in);
        size += count;
        if (ferror(in)) {
            fputs("MiniSat: input read error\n", stderr);
            free(data);
            exit(2);
        }
        if (feof(in))
            break;
    }
    /* Shrinking is optional: failure leaves the sufficient old buffer owned. */
    if (size + 1 < cap) {
        char *next = realloc(data, size + 1);
        if (next != NULL)
            data = next;
    }
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

static void readClause(char** in, solver* s, veci* lits) {
    int parsed_lit, var;


    veci_resize(lits,0);
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        veci_push(lits, (parsed_lit > 0 ? toLit(var) : lit_neg(toLit(var))));

    }

}

static lbool parse_DIMACS_main(char* in, solver* s) {
    veci lits;
    veci_new(&lits);

    for (;;){
        skipWhitespace(&in);
        if (*in == 0)
            break;
        else if (*in == 'c' || *in == 'p')
            skipLine(&in);
        else{
            lit* begin;
            readClause(&in, s, &lits);

            begin = veci_begin(&lits);
            if (veci_size(&lits) == 0 || !solver_addclause(s, begin, begin+veci_size(&lits))){
                veci_delete(&lits);
                return l_False;
            }
        }
    }
    veci_delete(&lits);

    return solver_simplify(s);
}


// Inserts problem into solver.
//
static lbool parse_DIMACS(FILE * in, solver* s) {
    char* text = readFile(in);
    lbool ret  = parse_DIMACS_main(text, s);
    free(text);
    return ret; }


//=================================================================================================


void printStats(stats* stats, clock_t cpu_time)
{
    double Time    = (float)(cpu_time)/(float)(CLOCKS_PER_SEC);
    printf("restarts          : %12llu\n", (unsigned long long)stats->starts);
    printf("conflicts         : %12.0f           (%9.0f / sec      )\n",  (double)stats->conflicts   , (double)stats->conflicts   /Time);
    printf("decisions         : %12.0f           (%9.0f / sec      )\n",  (double)stats->decisions   , (double)stats->decisions   /Time);
    printf("propagations      : %12.0f           (%9.0f / sec      )\n",  (double)stats->propagations, (double)stats->propagations/Time);
    printf("inspects          : %12.0f           (%9.0f / sec      )\n",  (double)stats->inspects    , (double)stats->inspects    /Time);
    printf("conflict literals : %12.0f           (%9.2f %% deleted  )\n", (double)stats->tot_literals, (double)(stats->max_literals - stats->tot_literals) * 100.0 / (double)stats->max_literals);
    printf("CPU time          : %12.2f sec\n", Time);
}

int main(int argc, char** argv)
{
    solver* s = solver_new();
    lbool   st;
    FILE *  in;
    clock_t clk = clock();

    if (argc != 2)
        fprintf(stderr, "ERROR! Not enough command line arguments.\n"),
        exit(1);

    in = fopen(argv[1], "rb");
    if (in == NULL)
        fprintf(stderr, "ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]),
        exit(1);
    st = parse_DIMACS(in, s);
    fclose(in);


    if (st == l_False){
        solver_delete(s);
        printf("Trivial problem\nUNSATISFIABLE\n");
        exit(20);
    }

    s->verbosity = 1;
    st = solver_solve(s,0,0);

    printStats(&s->stats, clock() - clk);
    printf("\n");
    printf(st == l_True ? "SATISFIABLE\n" : "UNSATISFIABLE\n");
    if ( st == l_True )
    {
        int k;
        printf("\nSatisfying solution: ");
        for (k = 0; k < s->model.size; k++)
            printf("x%d=%d ", k, s->model.ptr[k] == l_True);
        printf("\n");
    }
    solver_delete(s);
    return 0;
}
