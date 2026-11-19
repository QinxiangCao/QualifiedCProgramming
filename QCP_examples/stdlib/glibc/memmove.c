/* Copy memory to memory until the specified number of bytes
   has been copied.  Overlap is handled correctly.
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

/* Byte-copy verification adaptation of glibc 2.40 string/memmove.c.
 * The unsigned direction test is retained. Word-copy and page-copy fast
 * paths are replaced by the original BYTE_COPY_FWD/BWD loops, factored
 * into verified helpers. A zero-length early return avoids pointer casts.
 */
#include "memmove_loops.h"
/*@ Extern Coq
 (UCharArray::full : Z -> Z -> list Z -> Assertion)
 (UCharArray::undef_full : Z -> Z -> Assertion)
*/

/* Public contracts, with refinement links checked in this translation unit.
 * The standalone caller declarations are in memmove_spec.h. */
void *memmove(void *dest, const void *src, unsigned long long n)
/*@ separated <= byte_memory_spec
 With xs
 Require 0 <= n && Zlength(xs) == n &&
         0 <= src && src <= 18446744073709551615-n &&
         0 <= dest && dest <= 18446744073709551615-n &&
         UCharArray::full(src,n,xs) * UCharArray::undef_full(dest,n)
 Ensure __return == dest &&
        UCharArray::full(src,n,xs) * UCharArray::full(dest,n,xs)
*/;

void *memmove(void *dest, const void *src, unsigned long long n)
/*@ left_overlap <= byte_memory_spec
 With xs h
 Require Zlength(xs) == n && 0 < h && h < n &&
         src == pointer_offset(dest,h,unsigned char) &&
         0 <= dest && src <= 18446744073709551615-n &&
         UCharArray::undef_full(dest,h) * UCharArray::full(src,n,xs)
 Ensure __return == dest &&
        UCharArray::full(dest,n,xs) *
        UCharArray::full(pointer_offset(dest,n,unsigned char),h,sublist(n-h,n,xs))
*/;

void *memmove(void *dest, const void *src, unsigned long long n)
/*@ right_overlap <= byte_memory_spec
 With xs h
 Require Zlength(xs) == n && 0 < h && h < n &&
         dest == pointer_offset(src,h,unsigned char) &&
         0 <= src && dest <= 18446744073709551615-n &&
         UCharArray::full(src,n,xs) *
         UCharArray::undef_full(pointer_offset(src,n,unsigned char),h)
 Ensure __return == dest &&
        UCharArray::full(src,h,sublist(0,h,xs)) * UCharArray::full(dest,n,xs)
*/;

void *memmove(void *dest, const void *src, unsigned long long n)
/*@ same_range <= byte_memory_spec
 With xs
 Require 0 <= n && Zlength(xs) == n && dest == src &&
         0 <= src && src <= 18446744073709551615-n &&
         UCharArray::full(src,n,xs)
 Ensure __return == dest && UCharArray::full(src,n,xs)
*/;

void *memmove(void *dest, const void *src, unsigned long long n)
/*@ empty_copy <= byte_memory_spec
 Require n == 0 && emp
 Ensure __return == dest && emp
*/;


void *memmove(void *dest, const void *src, unsigned long long n)
/*@ byte_memory_spec
 With b1 n1 b2 n2 (m : mm_memory)
 Require 0 <= n && 0 <= n1 && 0 <= n2 &&
         (n == 0 || (0 <= src && src+n <= 18446744073709551615 &&
                     0 <= dest && dest+n <= 18446744073709551615)) &&
         mm_separated(b1,n1,b2,n2) && mm_access(m,src,dest,n,b1,n1,b2,n2) &&
         UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,m)) *
         UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,m))
 Ensure __return == dest &&
        UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,mm_snapshot(m,src,dest,n))) *
        UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,mm_snapshot(m,src,dest,n)))
*/
{
 if (n == 0) return dest;
 unsigned long long dstp = (unsigned long long)dest;
 unsigned long long srcp = (unsigned long long)src;
 if (dstp - srcp >= n) {
   mm_copy_forward((unsigned char *)dest,(const unsigned char *)src,n)
     /*@ where (direction_spec) b1=b1,n1=n1,b2=b2,n2=n2,m=m */;
 } else {
   mm_copy_backward((unsigned char *)dest,(const unsigned char *)src,n)
     /*@ where b1=b1,n1=n1,b2=b2,n2=n2,m=m */;
 }
 return dest;
}
