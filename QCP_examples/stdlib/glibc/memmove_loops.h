/* memcopy.h -- definitions for memory copy functions.  Generic C version.
   Copyright (C) 1991-2024 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <https://www.gnu.org/licenses/>.  */

/* glibc 2.40 memcopy.h BYTE_COPY_FWD/BWD, extracted as functions.
 * Byte loads and stores are factored through proved helpers. */
#include "memmove_bytes.h"
typedef unsigned long long size_t;
/*@ Extern Coq
 (mm_snapshot : mm_memory -> Z -> Z -> Z -> mm_memory)
 (mm_access : mm_memory -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
*/

/*@ Import Coq Require Import SimpleC.EE.stdlib.glibc.memmove_contract_lib */
/*@ Extern Coq (mm_forward_ok : Z -> Z -> Z -> Prop) */

void mm_copy_forward(unsigned char *dest, const unsigned char *src, size_t n)
/*@ direction_spec <= default
 With b1 n1 b2 n2 (m : mm_memory)
 Require 0 <= n && 0 <= n1 && 0 <= n2 &&
         0 <= src && src+n <= 18446744073709551615 &&
         0 <= dest && dest+n <= 18446744073709551615 &&
         mm_forward_ok(src,dest,n) &&
         mm_separated(b1,n1,b2,n2) && mm_access(m,src,dest,n,b1,n1,b2,n2) &&
         UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,m)) *
         UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,m))
 Ensure UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,mm_snapshot(m,src@pre,dest@pre,n@pre))) *
        UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,mm_snapshot(m,src@pre,dest@pre,n@pre)))
*/;

void mm_copy_forward(unsigned char *dest, const unsigned char *src, size_t n)
/*@ With b1 n1 b2 n2 (m : mm_memory)
 Require 0 <= n && 0 <= n1 && 0 <= n2 &&
         0 <= src && src+n <= 18446744073709551615 &&
         0 <= dest && dest+n <= 18446744073709551615 &&
         (dest <= src || src+n <= dest) &&
         mm_separated(b1,n1,b2,n2) && mm_access(m,src,dest,n,b1,n1,b2,n2) &&
         UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,m)) *
         UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,m))
 Ensure UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,mm_snapshot(m,src@pre,dest@pre,n@pre))) *
        UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,mm_snapshot(m,src@pre,dest@pre,n@pre)))
*/;

void mm_copy_backward(unsigned char *dest, const unsigned char *src, size_t n)
/*@ With b1 n1 b2 n2 (m : mm_memory)
 Require 0 <= n && 0 <= n1 && 0 <= n2 &&
         0 <= src && src+n <= 18446744073709551615 &&
         0 <= dest && dest+n <= 18446744073709551615 && src <= dest &&
         mm_separated(b1,n1,b2,n2) && mm_access(m,src,dest,n,b1,n1,b2,n2) &&
         UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,m)) *
         UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,m))
 Ensure UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,mm_snapshot(m,src@pre,dest@pre,n@pre))) *
        UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,mm_snapshot(m,src@pre,dest@pre,n@pre)))
*/;
