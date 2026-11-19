#ifndef GLIBC_AVAILABLE_H
#define GLIBC_AVAILABLE_H
#include "verification_stdlib.h"
#include "verification_list.h"
typedef unsigned long long probe_size_t;
/*@ Extern Coq (UCharArray::full : Z -> Z -> list Z -> Assertion)
               (tw_nonzero_bytes : list Z -> Prop)
               (tw_terminator : Z -> Z -> Assertion)
               (tw_probe_result : Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import SimpleC.EE.stdlib.glibc.two_way_dynamic_lib */

/* External libc primitive: exact bounded scan, preserving the complete
 * NUL-terminated allocation. Its implementation is a separate proof task. */
probe_size_t __strnlen(const unsigned char *s, probe_size_t limit)
/*@ With base bytes total offset
    Require s == base + offset && 0 <= offset && offset <= total &&
            total <= INT_MAX && 0 <= limit && limit <= 18446744073709551615 &&
            tw_nonzero_bytes(bytes) &&
            UCharArray::full(base, total, bytes) *
            tw_terminator(base, total)
    Ensure tw_probe_result(total, offset, limit, __return) &&
            0 <= __return && __return <= limit && offset + __return <= total &&
            (__return < limit => offset + __return == total) &&
            UCharArray::full(base, total, bytes) *
            tw_terminator(base, total)
*/;

int available(const unsigned char *h, probe_size_t *h_l,
              probe_size_t j, probe_size_t n_l)
/*@ With bytes total known
    Require 0 <= known && known <= total && total <= INT_MAX &&
            0 <= j && j <= known && 0 < n_l && n_l <= INT_MAX &&
            tw_nonzero_bytes(bytes) &&
            data_at(h_l, probe_size_t, known) *
            UCharArray::full(h, total, bytes) *
            tw_terminator(h, total)
    Ensure exists next,
            known <= next && next <= total &&
            ((__return == 1 && j + n_l <= next) ||
             (__return == 0 && next == total && total < j + n_l)) &&
            data_at(h_l, probe_size_t, next) *
            UCharArray::full(h, total, bytes) *
            tw_terminator(h, total)
*/;
#endif
