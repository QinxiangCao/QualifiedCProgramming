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

/*@ Extern Coq
      (vec_alloc_ok : Z -> Z -> Prop)
      (vec_growth_ok : Z -> Z -> Prop)
      (vec_push_result : Z -> Z -> Z -> Z -> Z -> Prop)
      (veci_raw : Z -> Z -> Z -> list Z -> Assertion)
      (store_veci : Z -> list Z -> Assertion)
      (veci_shell : Z -> Assertion)
      (vecp_raw : Z -> Z -> Z -> list Z -> Assertion)
      (store_vecp : Z -> list Z -> Assertion)
      (vecp_shell : Z -> Assertion)
 */
/*@ Import Coq Require Import vec_lib */

/* Success-only, typed allocator contracts.  They are the explicit trusted
   boundary required because the MiniSat implementation does not test OOM. */
void *malloc(unsigned int size)
/*@ malloc_int
  With (cap : Z)
  Require
    0 <= cap &&
    cap * sizeof(int) <= 4294967295 &&
    size == cap * sizeof(int)
  Ensure
    __return != 0 &&
    vec_alloc_ok(sizeof(int), cap) &&
    IntArray::undef_full(__return, cap)
*/
/*@ malloc_ptr
  With (cap : Z)
  Require
    0 <= cap &&
    cap * sizeof(void *) <= 4294967295 &&
    size == cap * sizeof(void *)
  Ensure
    __return != 0 &&
    vec_alloc_ok(sizeof(void *), cap) &&
    PtrArray::undef_full(__return, cap)
*/;

void *realloc(void *ptr, unsigned int size)
/*@ realloc_int
  With (xs : list Z) (oldcap : Z) (newcap : Z)
  Require
    0 <= Zlength(xs) && Zlength(xs) <= oldcap && oldcap <= newcap &&
    newcap * sizeof(int) <= 4294967295 &&
    size == newcap * sizeof(int) &&
    vec_alloc_ok(sizeof(int), newcap) &&
    IntArray::full(ptr, Zlength(xs), xs) *
    IntArray::undef_seg(ptr, Zlength(xs), oldcap)
  Ensure
    __return != 0 &&
    vec_alloc_ok(sizeof(int), newcap) &&
    IntArray::full(__return, Zlength(xs), xs) *
    IntArray::undef_seg(__return, Zlength(xs), newcap)
*/
/*@ realloc_ptr
  With (xs : list Z) (oldcap : Z) (newcap : Z)
  Require
    0 <= Zlength(xs) && Zlength(xs) <= oldcap && oldcap <= newcap &&
    newcap * sizeof(void *) <= 4294967295 &&
    size == newcap * sizeof(void *) &&
    vec_alloc_ok(sizeof(void *), newcap) &&
    PtrArray::full(ptr, Zlength(xs), xs) *
    PtrArray::undef_seg(ptr, Zlength(xs), oldcap)
  Ensure
    __return != 0 &&
    vec_alloc_ok(sizeof(void *), newcap) &&
    PtrArray::full(__return, Zlength(xs), xs) *
    PtrArray::undef_seg(__return, Zlength(xs), newcap)
*/;

void free(void *ptr)
/*@ free_int
  With (xs : list Z) (cap : Z)
  Require
    0 <= Zlength(xs) && Zlength(xs) <= cap &&
    IntArray::full(ptr, Zlength(xs), xs) *
    IntArray::undef_seg(ptr, Zlength(xs), cap)
  Ensure emp
*/
/*@ free_ptr
  With (xs : list Z) (cap : Z)
  Require
    0 <= Zlength(xs) && Zlength(xs) <= cap &&
    PtrArray::full(ptr, Zlength(xs), xs) *
    PtrArray::undef_seg(ptr, Zlength(xs), cap)
  Ensure emp
*/;

#include "vec.h"

void veci_new (veci* v)
/*@
  Require veci_shell(v)
  Ensure exists buf, veci_raw(v, buf, 4, nil)
*/
{
    /*@ veci_shell(v)
        which implies
        v != 0 &&
        undef_data_at(&(v->size), int) *
        undef_data_at(&(v->cap), int) *
        undef_data_at(&(v->ptr), int *)
     */
    v->size = 0;
    v->cap  = 4;
    v->ptr  = (int*)malloc(sizeof(int)*v->cap)
      /*@ where (malloc_int) cap = 4 */;
}

void veci_delete (veci* v)
/*@ With (xs : list Z)
    Require store_veci(v, xs)
    Ensure veci_shell(v)
*/
{
    /*@ store_veci(v, xs)
        which implies
        exists buf cap,
          v != 0 && buf != 0 &&
          0 <= Zlength(xs) && Zlength(xs) <= cap &&
          4 <= cap && cap <= 2147483647 &&
          vec_alloc_ok(sizeof(int), cap) &&
          store(&(v->size), int, Zlength(xs)) *
          store(&(v->cap), int, cap) *
          store(&(v->ptr), int *, buf) *
          IntArray::full(buf, Zlength(xs), xs) *
          IntArray::undef_seg(buf, Zlength(xs), cap)
     */
    free(v->ptr) /*@ where (free_int) xs = xs */;
}

int* veci_begin (veci* v)
/*@ With (xs : list Z)
    Require store_veci(v, xs)
    Ensure exists cap, veci_raw(v, __return, cap, xs)
*/
{
    /*@ store_veci(v, xs)
        which implies
        exists buf cap,
          v != 0 && buf != 0 &&
          0 <= Zlength(xs) && Zlength(xs) <= cap &&
          4 <= cap && cap <= 2147483647 &&
          vec_alloc_ok(sizeof(int), cap) &&
          store(&(v->size), int, Zlength(xs)) *
          store(&(v->cap), int, cap) *
          store(&(v->ptr), int *, buf) *
          IntArray::full(buf, Zlength(xs), xs) *
          IntArray::undef_seg(buf, Zlength(xs), cap)
     */
    return v->ptr;
}

int veci_size (veci* v)
/*@ With (xs : list Z)
    Require store_veci(v, xs)
    Ensure __return == Zlength(xs) && store_veci(v, xs)
*/
{
    /*@ store_veci(v, xs)
        which implies
        exists buf cap,
          v != 0 && buf != 0 &&
          0 <= Zlength(xs) && Zlength(xs) <= cap &&
          4 <= cap && cap <= 2147483647 &&
          vec_alloc_ok(sizeof(int), cap) &&
          store(&(v->size), int, Zlength(xs)) *
          store(&(v->cap), int, cap) *
          store(&(v->ptr), int *, buf) *
          IntArray::full(buf, Zlength(xs), xs) *
          IntArray::undef_seg(buf, Zlength(xs), cap)
     */
    return v->size;
}

void veci_resize (veci* v, int k)
/*@ With (xs : list Z) (buf : Z) (cap : Z)
    Require
      0 <= k && k <= Zlength(xs) &&
      veci_raw(v, buf, cap, xs)
    Ensure veci_raw(v, buf, cap, sublist(0, k, xs))
*/
{
    /*@ veci_raw(v, buf, cap, xs)
        which implies
        v != 0 && buf != 0 &&
        0 <= Zlength(xs) && Zlength(xs) <= cap &&
        4 <= cap && cap <= 2147483647 &&
        vec_alloc_ok(sizeof(int), cap) &&
        store(&(v->size), int, Zlength(xs)) *
        store(&(v->cap), int, cap) *
        store(&(v->ptr), int *, buf) *
        IntArray::full(buf, Zlength(xs), xs) *
        IntArray::undef_seg(buf, Zlength(xs), cap)
     */
    v->size = k;
} // only safe to shrink !!

void   veci_push   (veci* v, int e)
/*@ With (xs : list Z) (buf : Z) (cap : Z)
    Require
      veci_raw(v, buf, cap, xs) &&
      Zlength(xs) <= cap &&
      (Zlength(xs) == cap =>
        vec_growth_ok(sizeof(int), cap) &&
        cap <= 1073741823 &&
        (2 * cap + 1) * sizeof(int) <= 4294967295)
    Ensure
      exists buf2 cap2,
        veci_raw(v, buf2, cap2, app(xs, cons(e, nil))) &&
        vec_push_result(Zlength(xs), buf, cap, buf2, cap2)
*/
{
    /*@ veci_raw(v, buf, cap, xs)
        which implies
        v != 0 && buf != 0 &&
        0 <= Zlength(xs) && Zlength(xs) <= cap &&
        4 <= cap && cap <= 2147483647 &&
        vec_alloc_ok(sizeof(int), cap) &&
        store(&(v->size), int, Zlength(xs)) *
        store(&(v->cap), int, cap) *
        store(&(v->ptr), int *, buf) *
        IntArray::full(buf, Zlength(xs), xs) *
        IntArray::undef_seg(buf, Zlength(xs), cap)
     */
    if (v->size == v->cap) {
        int newsize = v->cap * 2+1;
        v->ptr = (int*)realloc(v->ptr,sizeof(int)*newsize)
          /*@ where (realloc_int)
                xs = xs, oldcap = cap, newcap = newsize */;
        v->cap = newsize; }
    /*@ Assert exists curbuf curcap,
          store(&(v->size), int, Zlength(xs)) *
          store(&(v->cap), int, curcap) *
          store(&(v->ptr), int *, curbuf) *
          IntArray::full(curbuf, Zlength(xs), xs) *
          IntArray::undef_seg(curbuf, Zlength(xs), curcap) &&
          v == v@pre &&
          e == e@pre &&
          v != 0 &&
          curbuf != 0 &&
          4 <= curcap &&
          curcap <= 2147483647 &&
          vec_alloc_ok(sizeof(int), curcap) &&
          Zlength(xs) <= cap &&
          Zlength(xs) < curcap &&
          (Zlength(xs) < cap => curbuf == buf && curcap == cap) &&
          (Zlength(xs) == cap => curcap == 2 * cap + 1)
     */
    v->ptr[v->size] = e;
    v->size++;
    /*@ exists curbuf curcap,
          store(&(v->size), int, Zlength(xs) + 1) *
          store(&(v->cap), int, curcap) *
          store(&(v->ptr), int *, curbuf) *
          IntArray::full(curbuf, Zlength(xs) + 1, app(xs, cons(e, nil))) *
          IntArray::undef_seg(curbuf, Zlength(xs) + 1, curcap) &&
          v == v@pre &&
          v != 0 &&
          curbuf != 0 &&
          4 <= curcap &&
          curcap <= 2147483647 &&
          vec_alloc_ok(sizeof(int), curcap) &&
          Zlength(xs) <= cap &&
          Zlength(xs) < curcap &&
          (Zlength(xs) < cap => curbuf == buf && curcap == cap) &&
          (Zlength(xs) == cap => curcap == 2 * cap + 1)
        which implies
        exists curbuf curcap,
          v == v@pre &&
          veci_raw(v@pre, curbuf, curcap, app(xs, cons(e, nil))) &&
          vec_push_result(Zlength(xs), buf, cap, curbuf, curcap)
     */
}


void vecp_new (vecp* v)
/*@
  Require vecp_shell(v)
  Ensure exists buf, vecp_raw(v, buf, 4, nil)
*/
{
    /*@ vecp_shell(v)
        which implies
        v != 0 &&
        undef_data_at(&(v->size), int) *
        undef_data_at(&(v->cap), int) *
        undef_data_at(&(v->ptr), void **)
     */
    v->size = 0;
    v->cap  = 4;
    v->ptr  = (void**)malloc(sizeof(void*)*v->cap)
      /*@ where (malloc_ptr) cap = 4 */;
}

void vecp_delete (vecp* v)
/*@ With (xs : list Z)
    Require store_vecp(v, xs)
    Ensure vecp_shell(v)
*/
{
    /*@ store_vecp(v, xs)
        which implies
        exists buf cap,
          v != 0 && buf != 0 &&
          0 <= Zlength(xs) && Zlength(xs) <= cap &&
          4 <= cap && cap <= 2147483647 &&
          vec_alloc_ok(sizeof(void *), cap) &&
          store(&(v->size), int, Zlength(xs)) *
          store(&(v->cap), int, cap) *
          store(&(v->ptr), void **, buf) *
          PtrArray::full(buf, Zlength(xs), xs) *
          PtrArray::undef_seg(buf, Zlength(xs), cap)
     */
    free(v->ptr) /*@ where (free_ptr) xs = xs */;
}

void** vecp_begin (vecp* v)
/*@ With (xs : list Z)
    Require store_vecp(v, xs)
    Ensure exists cap, vecp_raw(v, __return, cap, xs)
*/
{
    /*@ store_vecp(v, xs)
        which implies
        exists buf cap,
          v != 0 && buf != 0 &&
          0 <= Zlength(xs) && Zlength(xs) <= cap &&
          4 <= cap && cap <= 2147483647 &&
          vec_alloc_ok(sizeof(void *), cap) &&
          store(&(v->size), int, Zlength(xs)) *
          store(&(v->cap), int, cap) *
          store(&(v->ptr), void **, buf) *
          PtrArray::full(buf, Zlength(xs), xs) *
          PtrArray::undef_seg(buf, Zlength(xs), cap)
     */
    return v->ptr;
}

int vecp_size (vecp* v)
/*@ With (xs : list Z)
    Require store_vecp(v, xs)
    Ensure __return == Zlength(xs) && store_vecp(v, xs)
*/
{
    /*@ store_vecp(v, xs)
        which implies
        exists buf cap,
          v != 0 && buf != 0 &&
          0 <= Zlength(xs) && Zlength(xs) <= cap &&
          4 <= cap && cap <= 2147483647 &&
          vec_alloc_ok(sizeof(void *), cap) &&
          store(&(v->size), int, Zlength(xs)) *
          store(&(v->cap), int, cap) *
          store(&(v->ptr), void **, buf) *
          PtrArray::full(buf, Zlength(xs), xs) *
          PtrArray::undef_seg(buf, Zlength(xs), cap)
     */
    return v->size;
}

void vecp_resize (vecp* v, int k)
/*@ With (xs : list Z) (buf : Z) (cap : Z)
    Require
      0 <= k && k <= Zlength(xs) &&
      vecp_raw(v, buf, cap, xs)
    Ensure vecp_raw(v, buf, cap, sublist(0, k, xs))
*/
{
    /*@ vecp_raw(v, buf, cap, xs)
        which implies
        v != 0 && buf != 0 &&
        0 <= Zlength(xs) && Zlength(xs) <= cap &&
        4 <= cap && cap <= 2147483647 &&
        vec_alloc_ok(sizeof(void *), cap) &&
        store(&(v->size), int, Zlength(xs)) *
        store(&(v->cap), int, cap) *
        store(&(v->ptr), void **, buf) *
        PtrArray::full(buf, Zlength(xs), xs) *
        PtrArray::undef_seg(buf, Zlength(xs), cap)
     */
    v->size = k;
} // only safe to shrink !!

void   vecp_push   (vecp* v, void* e)
/*@ With (xs : list Z) (buf : Z) (cap : Z)
    Require
      vecp_raw(v, buf, cap, xs) &&
      Zlength(xs) <= cap &&
      (Zlength(xs) == cap =>
        vec_growth_ok(sizeof(void *), cap) &&
        cap <= 1073741823 &&
        (2 * cap + 1) * sizeof(void *) <= 4294967295)
    Ensure
      exists buf2 cap2,
        vecp_raw(v, buf2, cap2, app(xs, cons(e, nil))) &&
        vec_push_result(Zlength(xs), buf, cap, buf2, cap2)
*/
{
    /*@ vecp_raw(v, buf, cap, xs)
        which implies
        v != 0 && buf != 0 &&
        0 <= Zlength(xs) && Zlength(xs) <= cap &&
        4 <= cap && cap <= 2147483647 &&
        vec_alloc_ok(sizeof(void *), cap) &&
        store(&(v->size), int, Zlength(xs)) *
        store(&(v->cap), int, cap) *
        store(&(v->ptr), void **, buf) *
        PtrArray::full(buf, Zlength(xs), xs) *
        PtrArray::undef_seg(buf, Zlength(xs), cap)
     */
    if (v->size == v->cap) {
        int newsize = v->cap * 2+1;
        v->ptr = (void**)realloc(v->ptr,sizeof(void*)*newsize)
          /*@ where (realloc_ptr)
                xs = xs, oldcap = cap, newcap = newsize */;
        v->cap = newsize; }
    /*@ Assert exists curbuf curcap,
          store(&(v->size), int, Zlength(xs)) *
          store(&(v->cap), int, curcap) *
          store(&(v->ptr), void **, curbuf) *
          PtrArray::full(curbuf, Zlength(xs), xs) *
          PtrArray::undef_seg(curbuf, Zlength(xs), curcap) &&
          v == v@pre &&
          e == e@pre &&
          v != 0 &&
          curbuf != 0 &&
          4 <= curcap &&
          curcap <= 2147483647 &&
          vec_alloc_ok(sizeof(void *), curcap) &&
          Zlength(xs) <= cap &&
          Zlength(xs) < curcap &&
          (Zlength(xs) < cap => curbuf == buf && curcap == cap) &&
          (Zlength(xs) == cap => curcap == 2 * cap + 1)
     */
    v->ptr[v->size] = e;
    v->size++;
    /*@ exists curbuf curcap,
          store(&(v->size), int, Zlength(xs) + 1) *
          store(&(v->cap), int, curcap) *
          store(&(v->ptr), void **, curbuf) *
          PtrArray::full(curbuf, Zlength(xs) + 1, app(xs, cons(e, nil))) *
          PtrArray::undef_seg(curbuf, Zlength(xs) + 1, curcap) &&
          v == v@pre &&
          v != 0 &&
          curbuf != 0 &&
          4 <= curcap &&
          curcap <= 2147483647 &&
          vec_alloc_ok(sizeof(void *), curcap) &&
          Zlength(xs) <= cap &&
          Zlength(xs) < curcap &&
          (Zlength(xs) < cap => curbuf == buf && curcap == cap) &&
          (Zlength(xs) == cap => curcap == 2 * cap + 1)
        which implies
        exists curbuf curcap,
          v == v@pre &&
          vecp_raw(v@pre, curbuf, curcap, app(xs, cons(e, nil))) &&
          vec_push_result(Zlength(xs), buf, cap, curbuf, curcap)
     */
}
