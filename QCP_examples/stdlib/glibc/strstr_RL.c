/* Return the offset of one string within another.
   Copyright (C) 1994-2024 Free Software Foundation, Inc.
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

/* glibc 2.40 strstr composition. See upstream/string/strstr.c for copyright
 * and LGPL-2.1-or-later license. Source adaptations: QCP types/declarations,
 * scalar byte reads factored into a proved gs_read helper; short-loop update
 * spelled as a while loop; the Horspool body extracted to its proved function.
 * Two-Way retains the bounded int adapter used in its completed proof. */
#include "verification_stdlib.h"
#include "verification_list.h"
/*@ Import Coq Require Import SimpleC.EE.stdlib.glibc.strstr_lib */
/*@ Extern Coq
 (UCharArray::full : Z -> Z -> list Z -> Assertion)
 (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
 (Znth : {A} -> Z -> list A -> A -> A)
 (Zlength : {A} -> list A -> Z)
 (sublist : {A} -> Z -> Z -> list A -> list A)
 (gs_inputs : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (gs_bytes : list Z -> Prop)
 (hp_cstring : list Z -> Z -> Z -> Prop)
 (hp_inputs : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (hp_result : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (hp_no_match_before : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (hp_memcmp_result : list Z -> Z -> Z -> Z -> Z -> Prop)
 (gs_strchr : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (gs_short : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (gs_probe : Z -> Z -> Z -> Prop)
*/
typedef unsigned long long size_t;
typedef unsigned int uint32_t;

static unsigned char gs_read(const unsigned char *p)
/*@ With base length bytes index
 Require p == base + index && 0 <= index && index < length && gs_bytes(bytes) &&
         UCharArray::full(base, length, bytes)
 Ensure __return == Znth(index, bytes, 0) && 0 <= __return && __return < 256 &&
        UCharArray::full(base, length, bytes)
*/
{
 /*@ Assert p == base + index && 0 <= index && index < length && gs_bytes(bytes) &&
     UCharArray::seg(p, 0-index, length-index, bytes) */
 return p[0];
}

char *strchr(const char *s, int c)
/*@ With base length bytes ho hl
 Require s == base + ho && 0 <= ho && 0 <= hl && ho+hl < length &&
         0 < c && c < 256 && hp_cstring(bytes,ho,hl) &&
         UCharArray::full(base,length,bytes)
 Ensure gs_strchr(bytes,base,ho,hl,c,__return) && UCharArray::full(base,length,bytes)
*/;
size_t strlen(const char *s)
/*@ With base length bytes no nl
 Require s == base + no && 0 <= no && 0 <= nl && no+nl < length &&
         hp_cstring(bytes,no,nl) && UCharArray::full(base,length,bytes)
 Ensure __return == nl && UCharArray::full(base,length,bytes)
*/;
size_t __strnlen(const unsigned char *s, size_t limit)
/*@ With base length bytes ho hl
 Require s == base+ho && 0 <= ho && 0 <= hl && ho+hl < length &&
         hp_cstring(bytes,ho,hl) && UCharArray::full(base,length,bytes)
 Ensure gs_probe(hl,limit,__return) && UCharArray::full(base,length,bytes)
*/;
int memcmp(const void *s, const void *n, size_t count)
/*@ With base length bytes ho no
 Require s == base+ho && n == base+no && 0 <= ho && 0 <= no &&
         0 <= count && ho+count <= length && no+count <= length &&
         UCharArray::full(base,length,bytes)
 Ensure hp_memcmp_result(bytes,ho,no,count,__return) &&
        UCharArray::full(base,length,bytes)
*/;

static char *strstr2(const unsigned char *hs, const unsigned char *ne)
/*@ With base length bytes ho hl no
 Require hs == base+ho && ne == base+no && 0 < base && base+length <= UINT_MAX &&
         gs_inputs(bytes,length,ho,hl,no,2) && UCharArray::full(base,length,bytes)
 Ensure hp_result(bytes,base,ho,hl,no,2,__return) && UCharArray::full(base,length,bytes)
*/
{
 uint32_t h1 = (gs_read(ne) /*@ where base = base, length = length, bytes = bytes, index = no */ << 16) | gs_read(ne+1) /*@ where base = base, length = length, bytes = bytes, index = no+1 */;
 uint32_t h2 = 0;
 int c = gs_read(hs) /*@ where base = base, length = length, bytes = bytes, index = ho */;
 /*@ Inv Assert exists pos,
   ne == ne@pre && ne == base+no && hs == base+ho+pos &&
   0 < base && base+length <= UINT_MAX &&
   gs_inputs(bytes,length,ho,hl,no,2) &&
   gs_short(bytes,ho,hl,no,2,pos,h1,h2) &&
   0 <= pos && pos <= hl && c == Znth(ho+pos,bytes,0) && 0 <= c && c < 256 &&
   UCharArray::full(base,length,bytes) */
 while (h1 != h2 && c != 0)
 {
   h2 = (h2 << 16) | c;
   ++hs;
   c = gs_read(hs) /*@ where base = base, length = length, bytes = bytes, index = hs-base */;
 }
 return h1 == h2 ? (char *)hs - 2 : (char *)0;
}

static char *strstr3(const unsigned char *hs, const unsigned char *ne)
/*@ With base length bytes ho hl no
 Require hs == base+ho && ne == base+no && 0 < base && base+length <= UINT_MAX &&
         gs_inputs(bytes,length,ho,hl,no,3) && UCharArray::full(base,length,bytes)
 Ensure hp_result(bytes,base,ho,hl,no,3,__return) && UCharArray::full(base,length,bytes)
*/
{
 uint32_t h1 = ((uint32_t)gs_read(ne) /*@ where base = base, length = length, bytes = bytes, index = no */ << 24) | (gs_read(ne+1) /*@ where base = base, length = length, bytes = bytes, index = no+1 */ << 16) | (gs_read(ne+2) /*@ where base = base, length = length, bytes = bytes, index = no+2 */ << 8);
 uint32_t h2 = 0;
 int c = gs_read(hs) /*@ where base = base, length = length, bytes = bytes, index = ho */;
 /*@ Inv Assert exists pos,
   ne == ne@pre && ne == base+no && hs == base+ho+pos &&
   0 < base && base+length <= UINT_MAX &&
   gs_inputs(bytes,length,ho,hl,no,3) &&
   gs_short(bytes,ho,hl,no,3,pos,h1,h2) &&
   0 <= pos && pos <= hl && c == Znth(ho+pos,bytes,0) && 0 <= c && c < 256 &&
   UCharArray::full(base,length,bytes) */
 while (h1 != h2 && c != 0)
 {
   h2 = (h2 | c) << 8;
   ++hs;
   c = gs_read(hs) /*@ where base = base, length = length, bytes = bytes, index = hs-base */;
 }
 return h1 == h2 ? (char *)hs - 3 : (char *)0;
}
void *horspool_memmem_refinement(const void *haystack, size_t hs_len,
                      const void *needle, size_t ne_len)
/*@ 
    With base length bytes hayoff needleoff haylen
    Require haystack == base + hayoff * sizeof(unsigned char) &&
            needle == base + needleoff * sizeof(unsigned char) &&
            0 < base && base + length <= UINT_MAX &&
            0 <= hayoff && 0 <= needleoff && ne_len <= hs_len && hs_len <= haylen && hp_cstring(bytes, hayoff, haylen) &&
            3 <= ne_len && ne_len <= 256 && hayoff + haylen < length &&
            needleoff + ne_len <= length && length <= 2147483647 &&
            hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
            UCharArray::full(base, length, bytes)
    Ensure hp_result(bytes, base, hayoff, haylen, needleoff, ne_len, __return) &&
           UCharArray::full(base, length, bytes)
*/;


/* Shared-array adapter is implemented and verified in strstr_tw_bridge.c. */
void *strstr_tw_bridge(const unsigned char *hs, size_t known,
                       const unsigned char *ne, int nl)
/*@ With base length bytes ho hl no
 Require hs == base+ho && ne == base+no && 0 < base && base+length <= UINT_MAX &&
         gs_inputs(bytes,length,ho,hl,no,nl) && 256 < nl && nl <= known && known <= hl &&
         UCharArray::full(base,length,bytes)
 Ensure hp_result(bytes,base,ho,hl,no,nl,__return) && UCharArray::full(base,length,bytes)
*/;

char *strstr(const char *haystack, const char *needle)
/*@ With base length bytes ho hl no nl
 Require haystack == base+ho && needle == base+no &&
         0 < base && base+length <= UINT_MAX && gs_inputs(bytes,length,ho,hl,no,nl) &&
         UCharArray::full(base,length,bytes)
 Ensure hp_result(bytes,base,ho,hl,no,nl,__return) && UCharArray::full(base,length,bytes)
*/
{
 const unsigned char *hs = (const unsigned char *)haystack;
 const unsigned char *ne = (const unsigned char *)needle;
 if (gs_read(ne) /*@ where base = base, length = length, bytes = bytes, index = no */ == 0)
   return (char *)hs;
 hs = (const unsigned char *)strchr((const char *)hs, gs_read(ne) /*@ where base = base, length = length, bytes = bytes, index = no */)
   /*@ where base = base, length = length, bytes = bytes, ho = ho, hl = hl */;
 if (hs == 0) return (char *)hs;
 /*@ Assert exists start,
   haystack == base+ho && needle == base+no && ne == needle && hs == base+ho+start &&
   0 < base && base+length <= UINT_MAX && gs_inputs(bytes,length,ho,hl,no,nl) &&
   0 < nl && 0 <= start && start < hl &&
   Znth(ho+start,bytes,0) == Znth(no,bytes,0) &&
   hp_no_match_before(bytes,ho,hl,no,nl,start) &&
   UCharArray::full(base,length,bytes) */
 if (gs_read(ne+1) /*@ where base = base, length = length, bytes = bytes, index = no+1 */ == 0)
   return (char *)hs;
 if (gs_read(ne+2) /*@ where base = base, length = length, bytes = bytes, index = no+2 */ == 0)
   return strstr2(hs,ne) /*@ where base = base, length = length, bytes = bytes, ho = hs-base, hl = ho+hl-(hs-base), no = no */;
 if (gs_read(ne+3) /*@ where base = base, length = length, bytes = bytes, index = no+3 */ == 0)
   return strstr3(hs,ne) /*@ where base = base, length = length, bytes = bytes, ho = hs-base, hl = ho+hl-(hs-base), no = no */;
 size_t ne_len = strlen((const char *)ne) /*@ where base = base, length = length, bytes = bytes, no = no, nl = nl */;
 size_t hs_len = __strnlen(hs, ne_len | 512) /*@ where base = base, length = length, bytes = bytes, ho = hs-base, hl = ho+hl-(hs-base) */;
 if (hs_len < ne_len) return (char *)0;
 if (memcmp(hs,ne,ne_len) /*@ where base = base, length = length, bytes = bytes, ho = hs-base, no = no */ == 0)
   return (char *)hs;
 if (ne_len > 256)
   return strstr_tw_bridge(hs,hs_len,ne,(int)ne_len) /*@ where base = base, length = length, bytes = bytes, ho = hs-base, hl = ho+hl-(hs-base), no = no */;
 return horspool_memmem_refinement(hs,hs_len,ne,ne_len)
   /*@ where base = base, length = length, bytes = bytes, hayoff = hs-base, haylen = ho+hl-(hs-base), needleoff = no */;
}
