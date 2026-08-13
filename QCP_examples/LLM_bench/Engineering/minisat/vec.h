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

#ifndef vec_h
#define vec_h

void *malloc(unsigned int size);
void *realloc(void *ptr, unsigned int size);
void free(void *ptr);

// vector of 32-bit intergers (added for 64-bit portability)
struct veci_t {
    int    size;
    int    cap;
    int*   ptr;
};
typedef struct veci_t veci;

void veci_new    (veci* v);
void veci_delete (veci* v);
int* veci_begin  (veci* v);
int  veci_size   (veci* v);
void veci_resize (veci* v, int k); // only safe to shrink !!
void veci_push   (veci* v, int e);

// vector of 32- or 64-bit pointers
struct vecp_t {
    int    size;
    int    cap;
    void** ptr;
};
typedef struct vecp_t vecp;

void   vecp_new    (vecp* v);
void   vecp_delete (vecp* v);
void** vecp_begin  (vecp* v);
int    vecp_size   (vecp* v);
void   vecp_resize (vecp* v, int k); // only safe to shrink !!
void   vecp_push   (vecp* v, void* e);

#endif
