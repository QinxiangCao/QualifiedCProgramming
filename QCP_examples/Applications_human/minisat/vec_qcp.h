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

#include "minisat_qcp_compat.h"

/* Contracts for the inline vector bodies are frozen with this header. */
/*@ Extern Coq
      (vector_capacity_exhausted : Z -> Z -> Prop)
 */


// vector of 32-bit intergers (added for 64-bit portability)
struct veci_t {
    int    size;
    int    cap;
    int*   ptr;
};
typedef struct veci_t veci;

static inline void veci_new (veci* v)
/*@ Require undef_data_at(&(v->size), int) *
            undef_data_at(&(v->cap), int) *
            undef_data_at(&(v->ptr), int *)
    Ensure exists p,
             p != 0 &&
             store(&(v->size), int, 0) *
             store(&(v->cap), int, 4) *
             store(&(v->ptr), int *, p) *
             IntArray::seg(p, 0, 0, nil) *
             IntArray::undef_seg(p, 0, 4)
 */
{
    v->size = 0;
    v->cap  = 4;
    v->ptr = minisat_int_array_alloc(v->cap);
}

static inline void   veci_delete (veci* v)
/*@ With p (l : list Z) cap
    Require 0 <= Zlength(l) && Zlength(l) <= cap &&
            0 < cap && cap <= INT_MAX &&
            store(&(v->size), int, Zlength(l)) *
            store(&(v->cap), int, cap) *
            store(&(v->ptr), int *, p) *
            IntArray::seg(p, 0, Zlength(l), l) *
            IntArray::undef_seg(p, Zlength(l), cap)
    Ensure undef_data_at(&(v->size), int) *
           undef_data_at(&(v->cap), int) *
           undef_data_at(&(v->ptr), int *)
 */
{ minisat_int_array_free(v->ptr); }
static inline int*   veci_begin  (veci* v)
/*@ With p
    Require store(&(v->ptr), int *, p)
    Ensure __return == p && store(&(v->ptr), int *, p)
 */
{ return v->ptr;  }
static inline int    veci_size   (veci* v)
/*@ With n
    Require store(&(v->size), int, n)
    Ensure __return == n && store(&(v->size), int, n)
 */
{ return v->size; }
static inline void   veci_resize (veci* v, int k)
/*@ With p (l : list Z) cap
    Require 0 <= k && k <= Zlength(l) && Zlength(l) <= cap &&
            0 < cap && cap <= INT_MAX &&
            store(&(v->size), int, Zlength(l)) *
            store(&(v->cap), int, cap) *
            store(&(v->ptr), int *, p) *
            IntArray::seg(p, 0, Zlength(l), l) *
            IntArray::undef_seg(p, Zlength(l), cap)
    Ensure Zlength(sublist(0, k, l)) == k &&
           store(&(v->size), int, Zlength(sublist(0, k, l))) *
           store(&(v->cap), int, cap) *
           store(&(v->ptr), int *, p) *
           IntArray::seg(p, 0, Zlength(sublist(0, k, l)),
                         sublist(0, k, l)) *
           IntArray::undef_seg(p, Zlength(sublist(0, k, l)), cap)
 */
{ v->size = k;    } // only safe to shrink !!
static inline int minisat_next_capacity(int cap, int *next_cap)
/*@ Require 0 <= cap && cap <= INT_MAX && undef_data_at(next_cap, int)
    Ensure ((__return == 1 && 0 <= cap && cap <= 1073741823 &&
             store(next_cap, int, cap * 2 + 1)) ||
            (__return == -2 && 1073741823 < cap && cap <= INT_MAX &&
             undef_data_at(next_cap, int)))
 */
{
    assert(cap >= 0);
    if (cap > MINISAT_MAX_GROWABLE_CAP)
        return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    *next_cap = cap * 2 + 1;
    return 1;
}

static inline int veci_reserve(veci *v)
/*@ With p (l : list Z) cap
    Require 0 <= Zlength(l) && Zlength(l) <= cap &&
            0 < cap && cap <= INT_MAX &&
            store(&(v->size), int, Zlength(l)) *
            store(&(v->cap), int, cap) *
            store(&(v->ptr), int *, p) *
            IntArray::seg(p, 0, Zlength(l), l) *
            IntArray::undef_seg(p, Zlength(l), cap)
    Ensure ((__return == 1 &&
             (exists p_prime cap_prime,
                cap <= cap_prime && cap_prime <= INT_MAX &&
                Zlength(l) < cap_prime &&
                store(&(v->size), int, Zlength(l)) *
                store(&(v->cap), int, cap_prime) *
                store(&(v->ptr), int *, p_prime) *
                IntArray::seg(p_prime, 0, Zlength(l), l) *
                IntArray::undef_seg(p_prime, Zlength(l), cap_prime))) ||
            (__return == -2 &&
             Zlength(l) == cap &&
             1073741823 < cap &&
             vector_capacity_exhausted(Zlength(l), cap) &&
             store(&(v->size), int, Zlength(l)) *
             store(&(v->cap), int, cap) *
             store(&(v->ptr), int *, p) *
             IntArray::seg(p, 0, Zlength(l), l) *
             IntArray::undef_seg(p, Zlength(l), cap)))
 */
{
    int new_cap;
    int *new_ptr;

    if (v->size < v->cap)
        return 1;
    /*@ Zlength(l) == cap by local */
    assert(v->size == v->cap);
    if (minisat_next_capacity(v->cap, &new_cap) ==
        -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    new_ptr = minisat_int_array_realloc(v->ptr, v->cap, new_cap);
    v->ptr = new_ptr;
    v->cap = new_cap;
    return 1;
}

static inline int veci_push(veci *v, int element)
/*@ With p (l : list Z) cap
    Require 0 <= Zlength(l) && Zlength(l) <= cap &&
            0 < cap && cap <= INT_MAX &&
            store(&(v->size), int, Zlength(l)) *
            store(&(v->cap), int, cap) *
            store(&(v->ptr), int *, p) *
            IntArray::seg(p, 0, Zlength(l), l) *
            IntArray::undef_seg(p, Zlength(l), cap)
    Ensure ((__return == 1 &&
             (exists p_prime cap_prime,
                cap <= cap_prime && cap_prime <= INT_MAX &&
                Zlength(app(l, cons(element, nil))) <= cap_prime &&
                store(&(v->size), int,
                      Zlength(app(l, cons(element, nil)))) *
                store(&(v->cap), int, cap_prime) *
                store(&(v->ptr), int *, p_prime) *
                IntArray::seg(p_prime, 0,
                  Zlength(app(l, cons(element, nil))),
                  app(l, cons(element, nil))) *
                IntArray::undef_seg(p_prime,
                  Zlength(app(l, cons(element, nil))), cap_prime))) ||
            (__return == -2 &&
             Zlength(l) == cap &&
             1073741823 < cap &&
             vector_capacity_exhausted(Zlength(l), cap) &&
             store(&(v->size), int, Zlength(l)) *
             store(&(v->cap), int, cap) *
             store(&(v->ptr), int *, p) *
             IntArray::seg(p, 0, Zlength(l), l) *
             IntArray::undef_seg(p, Zlength(l), cap)))
 */
{
    int status = veci_reserve(v);
    if (status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        return status;
    v->ptr[v->size] = element;
    v->size++;
    return 1;
}


// vector of 32- or 64-bit pointers
struct vecp_t {
    int    size;
    int    cap;
    void** ptr;
};
typedef struct vecp_t vecp;

static inline void vecp_new (vecp* v)
/*@ Require undef_data_at(&(v->size), int) *
            undef_data_at(&(v->cap), int) *
            undef_data_at(&(v->ptr), void **)
    Ensure exists p,
             p != 0 &&
             store(&(v->size), int, 0) *
             store(&(v->cap), int, 4) *
             store(&(v->ptr), void **, p) *
             PtrArray::seg(p, 0, 0, nil) *
             PtrArray::undef_seg(p, 0, 4)
 */
{
    v->size = 0;
    v->cap  = 4;
    v->ptr = minisat_ptr_array_alloc(v->cap);
}

static inline void   vecp_delete (vecp* v)
/*@ With p (l : list Z) cap
    Require 0 <= Zlength(l) && Zlength(l) <= cap &&
            0 < cap && cap <= INT_MAX &&
            store(&(v->size), int, Zlength(l)) *
            store(&(v->cap), int, cap) *
            store(&(v->ptr), void **, p) *
            PtrArray::seg(p, 0, Zlength(l), l) *
            PtrArray::undef_seg(p, Zlength(l), cap)
    Ensure undef_data_at(&(v->size), int) *
           undef_data_at(&(v->cap), int) *
           undef_data_at(&(v->ptr), void **)
 */
{ minisat_ptr_array_free(v->ptr); }
static inline void** vecp_begin  (vecp* v)
/*@ With p
    Require store(&(v->ptr), void **, p)
    Ensure __return == p && store(&(v->ptr), void **, p)
 */
{ return v->ptr;  }
static inline int    vecp_size   (vecp* v)
/*@ With n
    Require store(&(v->size), int, n)
    Ensure __return == n && store(&(v->size), int, n)
 */
{ return v->size; }
static inline void   vecp_resize (vecp* v, int   k)
/*@ With p (l : list Z) cap
    Require 0 <= k && k <= Zlength(l) && Zlength(l) <= cap &&
            0 < cap && cap <= INT_MAX &&
            store(&(v->size), int, Zlength(l)) *
            store(&(v->cap), int, cap) *
            store(&(v->ptr), void **, p) *
            PtrArray::seg(p, 0, Zlength(l), l) *
            PtrArray::undef_seg(p, Zlength(l), cap)
    Ensure Zlength(sublist(0, k, l)) == k &&
           store(&(v->size), int, Zlength(sublist(0, k, l))) *
           store(&(v->cap), int, cap) *
           store(&(v->ptr), void **, p) *
           PtrArray::seg(p, 0, Zlength(sublist(0, k, l)),
                         sublist(0, k, l)) *
           PtrArray::undef_seg(p, Zlength(sublist(0, k, l)), cap)
 */
{ v->size = k;    } // only safe to shrink !!
static inline int vecp_reserve(vecp *v)
/*@ With p (l : list Z) cap
    Require 0 <= Zlength(l) && Zlength(l) <= cap &&
            0 < cap && cap <= INT_MAX &&
            store(&(v->size), int, Zlength(l)) *
            store(&(v->cap), int, cap) *
            store(&(v->ptr), void **, p) *
            PtrArray::seg(p, 0, Zlength(l), l) *
            PtrArray::undef_seg(p, Zlength(l), cap)
    Ensure ((__return == 1 &&
             (exists p_prime cap_prime,
                cap <= cap_prime && cap_prime <= INT_MAX &&
                Zlength(l) < cap_prime &&
                (Zlength(l) < cap => cap_prime == cap) &&
                store(&(v->size), int, Zlength(l)) *
                store(&(v->cap), int, cap_prime) *
                store(&(v->ptr), void **, p_prime) *
                PtrArray::seg(p_prime, 0, Zlength(l), l) *
                PtrArray::undef_seg(p_prime, Zlength(l), cap_prime))) ||
            (__return == -2 &&
             Zlength(l) == cap &&
             1073741823 < cap &&
             vector_capacity_exhausted(Zlength(l), cap) &&
             store(&(v->size), int, Zlength(l)) *
             store(&(v->cap), int, cap) *
             store(&(v->ptr), void **, p) *
             PtrArray::seg(p, 0, Zlength(l), l) *
             PtrArray::undef_seg(p, Zlength(l), cap)))
 */
{
    int new_cap;
    void **new_ptr;

    if (v->size < v->cap)
        return 1;
    /*@ Zlength(l) == cap by local */
    assert(v->size == v->cap);
    if (minisat_next_capacity(v->cap, &new_cap) ==
        -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        return -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE;
    new_ptr = minisat_ptr_array_realloc(v->ptr, v->cap, new_cap);
    v->ptr = new_ptr;
    v->cap = new_cap;
    return 1;
}

static inline int vecp_push(vecp *v, void *element)
/*@ With p (l : list Z) cap
    Require 0 <= Zlength(l) && Zlength(l) <= cap &&
            0 < cap && cap <= INT_MAX &&
            store(&(v->size), int, Zlength(l)) *
            store(&(v->cap), int, cap) *
            store(&(v->ptr), void **, p) *
            PtrArray::seg(p, 0, Zlength(l), l) *
            PtrArray::undef_seg(p, Zlength(l), cap)
    Ensure ((__return == 1 &&
             (exists p_prime cap_prime,
                cap <= cap_prime && cap_prime <= INT_MAX &&
                Zlength(app(l, cons(element, nil))) <= cap_prime &&
                (Zlength(l) < cap => cap_prime == cap) &&
                store(&(v->size), int, Zlength(app(l, cons(element, nil)))) *
                store(&(v->cap), int, cap_prime) *
                store(&(v->ptr), void **, p_prime) *
                PtrArray::seg(p_prime, 0,
                  Zlength(app(l, cons(element, nil))),
                  app(l, cons(element, nil))) *
                PtrArray::undef_seg(p_prime,
                  Zlength(app(l, cons(element, nil))), cap_prime))) ||
            (__return == -2 &&
             Zlength(l) == cap &&
             1073741823 < cap &&
             vector_capacity_exhausted(Zlength(l), cap) &&
             store(&(v->size), int, Zlength(l)) *
             store(&(v->cap), int, cap) *
             store(&(v->ptr), void **, p) *
             PtrArray::seg(p, 0, Zlength(l), l) *
             PtrArray::undef_seg(p, Zlength(l), cap)))
 */
{
    int status = vecp_reserve(v);
    if (status == -MINISAT_QCP_NEGATIVE_TWO_MAGNITUDE)
        return status;
    v->ptr[v->size] = element;
    v->size++;
    return 1;
}
