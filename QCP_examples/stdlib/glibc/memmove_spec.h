/* Public contracts for the byte-copy adaptation of glibc memmove.
 * No private memory or Monad predicates occur in these contracts. */
#include "verification_stdlib.h"
#include "verification_list.h"
/*@ Extern Coq
 (UCharArray::full : Z -> Z -> list Z -> Assertion)
 (UCharArray::undef_full : Z -> Z -> Assertion)
*/

void *memmove(void *dest, const void *src, unsigned long long n)
/*@ separated
 With xs
 Require 0 <= n && Zlength(xs) == n &&
         0 <= src && src <= 18446744073709551615-n &&
         0 <= dest && dest <= 18446744073709551615-n &&
         UCharArray::full(src,n,xs) * UCharArray::undef_full(dest,n)
 Ensure __return == dest &&
        UCharArray::full(src,n,xs) * UCharArray::full(dest,n,xs)
*/;

void *memmove(void *dest, const void *src, unsigned long long n)
/*@ left_overlap
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
/*@ right_overlap
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
/*@ same_range
 With xs
 Require 0 <= n && Zlength(xs) == n && dest == src &&
         0 <= src && src <= 18446744073709551615-n &&
         UCharArray::full(src,n,xs)
 Ensure __return == dest && UCharArray::full(src,n,xs)
*/;

void *memmove(void *dest, const void *src, unsigned long long n)
/*@ empty_copy
 Require n == 0 && emp
 Ensure __return == dest && emp
*/;
