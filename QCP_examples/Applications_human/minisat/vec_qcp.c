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

// The vector operations of vec_qcp.h, verified once as their own unit.

#include "vec_qcp_runtime.h"
#include "vec_qcp.h"

void veci_new(veci* v)
/*@ default */
{
    v->size = 0;
    v->cap  = 0;
    v->ptr = NULL;
}

void veci_delete(veci* v)
/*@ default */
{
    vec_int_array_free(v->ptr);
}

int* veci_begin(veci* v)
/*@ default */
{
    return v->ptr;
}

int veci_size(veci* v)
/*@ default */
{
    return v->size;
}

void veci_resize(veci* v, int k)
/*@ default */
{
    v->size = k; // Only safe to shrink.
}

int vec_next_capacity(int cap)
/*@ default */
{
    if (cap == 2147483647)
        vec_resource_stop();
    if (cap > VEC_MAX_GROWABLE_CAP)
        return cap + 1;
    return cap * 2 + 1;
}

void veci_push(veci *v, int e)
/*@ default */
{
    if (v->size == v->cap) {
        int new_cap = vec_next_capacity(v->cap);
        v->ptr = vec_int_array_realloc(v->ptr, v->cap, &new_cap);
        v->cap = new_cap;
    }
    /*@ v->size < v->cap by local */
    v->ptr[v->size] = e;
    v->size++;
}

void vecp_new(vecp* v)
/*@ default */
{
    v->size = 0;
    v->cap  = 4;
    v->ptr = vec_ptr_array_alloc(v->cap);
}

void vecp_delete(vecp* v)
/*@ default */
{
    vec_ptr_array_free(v->ptr);
}

void** vecp_begin(vecp* v)
/*@ default */
{
    return v->ptr;
}

int vecp_size(vecp* v)
/*@ default */
{
    return v->size;
}

void vecp_resize(vecp* v, int k)
/*@ default */
{
    v->size = k; // Only safe to shrink.
}

void vecp_push(vecp *v, void * e)
/*@ default */
{
    if (v->size == v->cap) {
        int new_cap = vec_next_capacity(v->cap);
        v->ptr = vec_ptr_array_realloc(v->ptr, v->cap, &new_cap);
        v->cap = new_cap;
    }
    /*@ v->size < v->cap by local */
    v->ptr[v->size] = e;
    v->size++;
}

/* Remove the first occurrence of e, preserving the order of the other elements. */
void vecp_remove(vecp* v, void* e)
/*@ default */
{
    void** ws = vecp_begin(v);
    int    j  = 0;

    /*@ Inv Assert e == e@pre && v == v@pre &&
                   vecp_remove_scan_inv(e, l, j) &&
                   0 <= j && j < Zlength(l) &&
                   Vecp::rep_ptr(v, ws, l)
     */
    for (; ws[j] != e  ; j++);
    assert(j < vecp_size(v));
    /*@ Inv Assert exists found (words_now : list Z),
                   e == e@pre && v == v@pre &&
                   vecp_remove_shift_inv(e, l, found, j, words_now) &&
                   0 <= j && j < Zlength(words_now) &&
                   Vecp::rep_ptr(v, ws, words_now)
     */
    for (; j < vecp_size(v)-1; j++) ws[j] = ws[j+1];
    /*@ Given found words_now */
    /*@ vecp_remove_shift_inv(e, l, found, j, words_now) &&
          j >= Zlength(words_now) - 1 &&
          j < Zlength(words_now)
        which implies
          first_occurrence(e, l, found) &&
          1 <= Zlength(words_now) &&
          sublist(0, Zlength(words_now) - 1, words_now) ==
            remove_nth(found, l) &&
          has_permission(&j)
     */
    vecp_resize(v,vecp_size(v)-1);
}
