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
*/
{
 size_t remaining = n;
 /*@ Inv Assert exists i,
   0 <= i && i <= n@pre && n == n@pre && remaining == n@pre-i &&
   src == src@pre+i && dest == dest@pre+i &&
   0 <= n1 && 0 <= n2 &&
   0 <= src@pre && src@pre+n@pre <= 18446744073709551615 &&
   0 <= dest@pre && dest@pre+n@pre <= 18446744073709551615 &&
   (dest@pre <= src@pre || src@pre+n@pre <= dest@pre) &&
   mm_separated(b1,n1,b2,n2) && mm_access(m,src@pre,dest@pre,n@pre,b1,n1,b2,n2) &&
   UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,mm_snapshot(m,src@pre,dest@pre,i))) *
   UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,mm_snapshot(m,src@pre,dest@pre,i))) */
 while (remaining > 0) {
   unsigned char x = mm_load_byte(src) /*@ where b1=b1,n1=n1,b2=b2,n2=n2,m=mm_snapshot(m,src@pre,dest@pre,n@pre-remaining) */;
   src += 1;
   remaining -= 1;
   mm_store_byte(dest,x) /*@ where b1=b1,n1=n1,b2=b2,n2=n2,m=mm_snapshot(m,src@pre,dest@pre,n@pre-remaining-1) */;
   dest += 1;
 }
}

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
*/
{
 src += n;
 dest += n;
 size_t remaining = n;
 /*@ Inv Assert
   0 <= remaining && remaining <= n@pre && n == n@pre &&
   src == src@pre+remaining && dest == dest@pre+remaining &&
   0 <= n1 && 0 <= n2 &&
   0 <= src@pre && src@pre+n@pre <= 18446744073709551615 &&
   0 <= dest@pre && dest@pre+n@pre <= 18446744073709551615 && src@pre <= dest@pre &&
   mm_separated(b1,n1,b2,n2) && mm_access(m,src@pre,dest@pre,n@pre,b1,n1,b2,n2) &&
   UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,mm_snapshot(m,src@pre+remaining,dest@pre+remaining,n@pre-remaining))) *
   UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,mm_snapshot(m,src@pre+remaining,dest@pre+remaining,n@pre-remaining))) */
 while (remaining > 0) {
   src -= 1;
   unsigned char x = mm_load_byte(src) /*@ where b1=b1,n1=n1,b2=b2,n2=n2,m=mm_snapshot(m,src@pre+remaining,dest@pre+remaining,n@pre-remaining) */;
   dest -= 1;
   remaining -= 1;
   mm_store_byte(dest,x) /*@ where b1=b1,n1=n1,b2=b2,n2=n2,m=mm_snapshot(m,src@pre+remaining+1,dest@pre+remaining+1,n@pre-(remaining+1)) */;
 }
}
