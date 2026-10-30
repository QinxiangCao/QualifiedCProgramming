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

#include "vec_qcp_def.h"

/* Veci::rep(v, l) and Vecp::rep(v, l): the vector at v holds l; buffer and
   capacity are hidden. Veci::rep_ptr(v, p, l) also names its buffer p;
   Veci::header(v, p, n, cap) is its struct (length n, capacity cap, buffer p)
   while the strategies hold the buffer open. A vector
   without capacity stores NULL (vec_buf_ok). rep does not record that the
   buffer came from the allocator: veci_delete and vecp_delete free it, so they
   are safe only on vectors made by veci_new or vecp_new and grown by push. A
   client-built rep over a stack or interior buffer meets their contracts but
   not libc free. Both are instances of DynVec
   (dynvec_lib.v, vec_qcp_lib.v); the strategies below open and close them.
   The operations are verified once, in vec_qcp.c; clients see only these
   contracts, which must stay identical to vec_qcp.c's. */

/*@ include strategies "vec_qcp.strategies" */

// vector of 32-bit integers (added for 64-bit portability)
struct veci_t {
    int    size;
    int    cap;
    int*   ptr;
};
typedef struct veci_t veci;

void veci_new(veci* v)
/*@ Require Veci::shell(v)
    Ensure Veci::rep(v, nil)
 */;

void veci_delete(veci* v)
/*@ With (l : list Z)
    Require Veci::rep(v, l)
    Ensure Veci::shell(v)
 */;

int* veci_begin(veci* v)
/*@ With p (l : list Z)
    Require Veci::rep_ptr(v, p, l)
    Ensure __return == p && Veci::rep_ptr(v, p, l)
 */;

int veci_size(veci* v)
/*@ With p (l : list Z)
    Require Veci::rep_ptr(v, p, l)
    Ensure __return == Zlength(l) && Veci::rep_ptr(v, p, l)
 */;

void veci_resize(veci* v, int k)
/*@ With p (l : list Z)
    Require 0 <= k && k <= Zlength(l) && Veci::rep_ptr(v, p, l)
    Ensure Zlength(sublist(0, k, l)) == k &&
           Veci::rep_ptr(v, p, sublist(0, k, l))
 */;

int vec_next_capacity(int cap)
/*@ Require 0 <= cap && cap <= INT_MAX && emp
    Ensure cap < __return && __return <= INT_MAX &&
           ((__return == cap * 2 + 1 && cap <= 1073741823) ||
            (__return == cap + 1 && cap > 1073741823)) && emp
 */;

void veci_push(veci *v, int e)
/*@ With (l : list Z)
    Require Veci::rep(v, l)
    Ensure Veci::rep(v, app(l, cons(e, nil)))
 */;


// vector of 32- or 64-bit pointers
struct vecp_t {
    int    size;
    int    cap;
    void** ptr;
};
typedef struct vecp_t vecp;

void vecp_new(vecp* v)
/*@ Require Vecp::shell(v)
    Ensure Vecp::rep(v, nil)
 */;

void vecp_delete(vecp* v)
/*@ With (l : list Z)
    Require Vecp::rep(v, l)
    Ensure Vecp::shell(v)
 */;

void** vecp_begin(vecp* v)
/*@ With p (l : list Z)
    Require Vecp::rep_ptr(v, p, l)
    Ensure __return == p && Vecp::rep_ptr(v, p, l)
 */;

int vecp_size(vecp* v)
/*@ With p (l : list Z)
    Require Vecp::rep_ptr(v, p, l)
    Ensure __return == Zlength(l) && Vecp::rep_ptr(v, p, l)
 */;

void vecp_resize(vecp* v, int k)
/*@ With p (l : list Z)
    Require 0 <= k && k <= Zlength(l) && Vecp::rep_ptr(v, p, l)
    Ensure Zlength(sublist(0, k, l)) == k &&
           Vecp::rep_ptr(v, p, sublist(0, k, l))
 */;

void vecp_push(vecp *v, void * e)
/*@ With (l : list Z)
    Require Vecp::rep(v, l)
    Ensure Vecp::rep(v, app(l, cons(e, nil)))
 */;

/* Remove the first occurrence of e, preserving the order of the other elements. */
void vecp_remove(vecp* v, void* e)
/*@ With (l : list Z)
    Require In(e, l) && Vecp::rep(v, l)
    Ensure exists k, first_occurrence(e, l, k) && Vecp::rep(v, remove_nth(k, l))
 */;

#endif /* vec_h */
