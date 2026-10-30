/* Trusted runtime boundary of the vector library (vec_qcp.h / vec_qcp.c): buffer
   allocation for int and pointer elements, resource exhaustion and assert. Nothing
   here is specific to a client. On the verification path these are contracts; with
   VEC_QCP_NATIVE_RUNTIME they are libc-backed, and every translation unit of a
   native build (vec_qcp.c included) must be compiled with it. A normal return
   never reports failure: resource exhaustion terminates the process.
   Allocation origin is not represented. The buffer contracts own cells only, so
   they cannot tell a buffer returned here from a stack, global or interior
   pointer, for which libc free and realloc are undefined. Callers must pass a
   buffer returned by these functions. The vector operations of vec_qcp.c pass
   the buffer held in the vector, so this holds for vectors made by veci_new or
   vecp_new (see vec_qcp.h). A buffer without capacity must be NULL, which the
   contracts below require. */
#ifndef VEC_QCP_RUNTIME_H
#define VEC_QCP_RUNTIME_H

#include "verification_stdlib.h"

#ifdef VEC_QCP_NATIVE_RUNTIME
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#endif

#ifndef NULL
#define NULL 0
#endif

/* Largest capacity that vec_next_capacity still doubles (2 * cap + 1 <= INT_MAX). */
#define VEC_MAX_GROWABLE_CAP 1073741823

/* Trusted normal-return boundary. Resource failure terminates the process. */
#ifndef VEC_QCP_NATIVE_RUNTIME
void vec_resource_stop(void)
/*@ Require emp
    Ensure 0 == 1 && emp
 */;
#endif

int *vec_int_array_realloc(int *p, int old_cap, int *new_cap)
/*@ With size l preferred
    Require 0 <= size && size == old_cap && old_cap < preferred &&
            (old_cap == 0 => p == 0) &&
            store(new_cap, int, preferred) *
            IntArray::seg(p, 0, size, l)
    Ensure exists actual,
           __return != 0 && old_cap < actual && actual <= preferred &&
           (actual == preferred || actual == old_cap + 1) &&
           store(new_cap, int, actual) *
           IntArray::seg(__return, 0, size, l) *
           IntArray::undef_seg(__return, size, actual)
 */;

void vec_int_array_free(int *p)
/*@ With size cap l
    Require 0 <= size && size <= cap && (cap == 0 => p == 0) &&
            IntArray::seg(p, 0, size, l) *
            IntArray::undef_seg(p, size, cap)
    Ensure emp
 */;

void **vec_ptr_array_alloc(int cap)
/*@ Require cap > 0 && emp
    Ensure __return != 0 && PtrArray::undef_full(__return, cap)
 */;

void **vec_ptr_array_realloc(void **p, int old_cap, int *new_cap)
/*@ With size l preferred
    Require 0 <= size && size == old_cap && old_cap < preferred &&
            (old_cap == 0 => p == 0) &&
            store(new_cap, int, preferred) *
            PtrArray::seg(p, 0, size, l)
    Ensure exists actual,
           __return != 0 && old_cap < actual && actual <= preferred &&
           (actual == preferred || actual == old_cap + 1) &&
           store(new_cap, int, actual) *
           PtrArray::seg(__return, 0, size, l) *
           PtrArray::undef_seg(__return, size, actual)
 */;

void vec_ptr_array_free(void **p)
/*@ With size cap l
    Require 0 <= size && size <= cap && (cap == 0 => p == 0) &&
            PtrArray::seg(p, 0, size, l) *
            PtrArray::undef_seg(p, size, cap)
    Ensure emp
 */;

void qcp_assert(int expr)
/*@ Require expr != 0 && emp
    Ensure emp
 */;
#ifndef VEC_QCP_NATIVE_RUNTIME
#define assert(expr) qcp_assert(expr)
#endif

#ifdef VEC_QCP_NATIVE_RUNTIME
static inline void vec_resource_stop(void)
{
    fputs("resource exhaustion\n", stderr);
    exit(2);
}

static inline void *vec_checked_alloc(size_t count, size_t unit, size_t extra)
{
    void *p;
    if (unit == 0 || count > (SIZE_MAX - extra) / unit)
        vec_resource_stop();
    p = malloc(count * unit + extra);
    if (p == NULL)
        vec_resource_stop();
    return p;
}

/* A failed realloc retains p. Try a strictly smaller minimum only once.
   The in/out count also lowers all remaining requests in a growth batch. */
static inline void *vec_checked_grow(void *p, int required,
                                        int *capacity, size_t unit)
{
    int preferred = *capacity;
    void *q = NULL;
    if (required <= 0 || preferred < required || unit == 0)
        vec_resource_stop();
    if ((size_t)preferred <= SIZE_MAX / unit)
        q = realloc(p, (size_t)preferred * unit);
    if (q != NULL)
        return q;
    if (required < preferred && (size_t)required <= SIZE_MAX / unit) {
        q = realloc(p, (size_t)required * unit);
        if (q != NULL) {
            *capacity = required;
            return q;
        }
    }
    vec_resource_stop();
    return NULL;
}

#define vec_int_array_realloc(p, old_cap, new_cap) \
    ((int *)vec_checked_grow((p), (old_cap) + 1, (new_cap), sizeof(int)))
#define vec_int_array_free(p) free(p)
#define vec_ptr_array_alloc(cap) \
    ((void **)vec_checked_alloc((cap), sizeof(void *), 0))
#define vec_ptr_array_realloc(p, old_cap, new_cap) \
    ((void **)vec_checked_grow((p), (old_cap) + 1, (new_cap), sizeof(void *)))
#define vec_ptr_array_free(p) free(p)
#endif

#endif /* VEC_QCP_RUNTIME_H */
