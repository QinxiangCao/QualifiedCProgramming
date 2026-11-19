/* Copyright (C) 1991-2024 Free Software Foundation, Inc.
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

/* Verification adaptation of glibc 2.40 strstr's 3..256-byte needle path.
   hp_hash2, size_t spelling, shared-array contracts and search_end naming are
   inherited from the checked fixed-length case. The only executable change
   from that case restores strstr's original 2048-byte frontier extension.
   haylen is logical only; hs_len is the initial discovered prefix length. */
#include "verification_stdlib.h"
#include "verification_list.h"
/*@ Import Coq Require Import SimpleC.EE.stdlib.glibc.horspool_dynamic_lib */
/*@ Import Coq Local Open Scope monad */
/*@ Extern Coq (program :: * => * => *) (unit :: *) */
/*@ Extern Coq
 (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop)
 (return : {Sigma} {A} -> A -> program Sigma A)
 (ATrue : {A} -> A -> Prop)
 (hp_search_from : list Z -> Z -> Z -> Z -> Z -> Z -> program unit (option Z))
 (hp_ptr_result : Z -> Z -> option Z)
*/
/*@ Printing Coq Name program := MonadErr.M */
/*@ Printing Strategy Name program := MonadErr.M */
/*@ Extern Coq
 (UCharArray::full : Z -> Z -> list Z -> Assertion)
 (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
 (UCharArray::undef_full : Z -> Z -> Assertion)
 (repeat_Z : {A} -> A -> Z -> list A)
 (hp_hash_at : list Z -> Z -> Z)
 (hp_cstring : list Z -> Z -> Z -> Prop)
 (hp_probe_result : Z -> Z -> Z -> Z -> Prop)
 (hp_inputs : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (hp_result : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (hp_no_match_before : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (hp_table_prefix : list Z -> Z -> Z -> list Z -> Prop)
 (hp_table_final : list Z -> Z -> Z -> list Z -> Z -> Prop)
 (hp_filter_offset : Z -> Z -> Prop)
 (hp_memcmp_result : list Z -> Z -> Z -> Z -> Z -> Prop)
*/
typedef unsigned long long size_t;
typedef unsigned char uint8_t;

static size_t hp_hash2(const unsigned char *pointer)
/*@ With base length bytes index
    Require pointer == base + index * sizeof(unsigned char) && 1 <= index && index < length &&
            UCharArray::full(base, length, bytes)
    Ensure __return == hp_hash_at(bytes, index) && 0 <= __return && __return < 256 &&
           UCharArray::full(base, length, bytes)
*/
{
  /*@ Assert pointer == pointer@pre && pointer == base + index * sizeof(unsigned char) &&
      1 <= index && index < length && UCharArray::seg(pointer, 0 - index, length - index, bytes) */
  return ((size_t)pointer[0] - ((size_t)pointer[-1] << 3)) % 256;
}

void *memset(void *destination, int value, size_t count)
/*@ With address
    Require destination == address && value == 0 && count == 256 && UCharArray::undef_full(address, 256)
    Ensure __return == destination && UCharArray::full(address, 256, repeat_Z(0, 256))
*/;

int memcmp(const unsigned char *left, const unsigned char *right, size_t count)
/*@ With base length bytes leftoff rightoff
    Require left == base + leftoff && right == base + rightoff &&
            0 <= leftoff && 0 <= rightoff && 0 <= count &&
            leftoff + count <= length && rightoff + count <= length &&
            UCharArray::full(base, length, bytes)
    Ensure hp_memcmp_result(bytes, leftoff, rightoff, count, __return) &&
           INT_MIN <= __return && __return <= INT_MAX &&
           UCharArray::full(base, length, bytes)
*/;

/* External dependency: bounded NUL scan on the shared array. The terminator
   is part of that array, allowing haystack and needle to share storage. */
size_t __strnlen(const unsigned char *s, size_t count)
/*@ With base length bytes hayoff haylen start
    Require s == base + hayoff + start && 0 <= hayoff &&
            0 <= start && start <= haylen && hayoff + haylen < length &&
            hp_cstring(bytes, hayoff, haylen) &&
            UCharArray::full(base, length, bytes)
    Ensure hp_probe_result(haylen, start, count, __return) &&
           UCharArray::full(base, length, bytes)
*/;

void *horspool_memmem_refinement(const void *haystack, size_t hs_len,
                      const void *needle, size_t ne_len)
/*@ high_level_spec <= low_level_spec
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

void *horspool_memmem_refinement(const void *haystack, size_t hs_len,
                      const void *needle, size_t ne_len)
/*@ low_level_spec
    With base length bytes hayoff needleoff haylen X
    Require haystack == base + hayoff * sizeof(unsigned char) &&
            needle == base + needleoff * sizeof(unsigned char) &&
            0 < base && base + length <= UINT_MAX &&
            0 <= hayoff && 0 <= needleoff && ne_len <= hs_len && hs_len <= haylen && hp_cstring(bytes, hayoff, haylen) &&
            3 <= ne_len && ne_len <= 256 && hayoff + haylen < length &&
            needleoff + ne_len <= length && length <= 2147483647 &&
            hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
            safeExec(ATrue, hp_search_from(bytes, hayoff, haylen, needleoff, ne_len, 0), X) &&
            UCharArray::full(base, length, bytes)
    Ensure safeExec(ATrue, return(hp_ptr_result(base + hayoff, __return)), X) &&
           UCharArray::full(base, length, bytes)
*/
{
  const unsigned char *hs = (const unsigned char *)haystack;
  const unsigned char *ne = (const unsigned char *)needle;
  if (hs_len < ne_len)
    return (void *)0;
  const unsigned char *search_end = hs + hs_len - ne_len;
  unsigned char shift[256];
  size_t tmp = 0, shift1 = 0;
  size_t m1 = ne_len - 1;
  size_t offset = 0;
  memset(shift, 0, 256) /*@ where address = shift */;
  /*@ Assert haystack == haystack@pre && needle == needle@pre &&
      hs_len == hs_len@pre && ne_len == ne_len@pre &&
      haystack == base + hayoff * sizeof(unsigned char) &&
      needle == base + needleoff * sizeof(unsigned char) &&
      0 < base && base + length <= UINT_MAX &&
      0 <= hayoff && 0 <= needleoff && 3 <= ne_len && ne_len <= 256 &&
      ne_len <= hs_len && hs_len <= haylen && hp_cstring(bytes, hayoff, haylen) && hayoff + haylen < length && needleoff + ne_len <= length &&
      length <= 2147483647 && hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
      safeExec(ATrue, hp_search_from(bytes, hayoff, haylen, needleoff, ne_len, 0), X) &&
      ne == needle && m1 == ne_len - 1 && 2 <= m1 && m1 <= 255 &&
      search_end == haystack + (hs_len - ne_len) * sizeof(unsigned char) && hs == haystack && offset == 0 &&
      UCharArray::full(base, length, bytes) * UCharArray::full(shift, 256, repeat_Z(0,256)) && tmp == 0 && shift1 == 0 */
  /*@ Inv Assert exists table, haystack == haystack@pre && needle == needle@pre &&
      hs_len == hs_len@pre && ne_len == ne_len@pre &&
      haystack == base + hayoff * sizeof(unsigned char) &&
      needle == base + needleoff * sizeof(unsigned char) &&
      0 < base && base + length <= UINT_MAX &&
      0 <= hayoff && 0 <= needleoff && 3 <= ne_len && ne_len <= 256 &&
      ne_len <= hs_len && hs_len <= haylen && hp_cstring(bytes, hayoff, haylen) && hayoff + haylen < length && needleoff + ne_len <= length &&
      length <= 2147483647 && hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
      safeExec(ATrue, hp_search_from(bytes, hayoff, haylen, needleoff, ne_len, 0), X) &&
      ne == needle && m1 == ne_len - 1 && 2 <= m1 && m1 <= 255 &&
      search_end == haystack + (hs_len - ne_len) * sizeof(unsigned char) && hs == haystack && offset == 0 &&
      1 <= i && i <= m1 && hp_table_prefix(bytes, needleoff, i, table) && UCharArray::full(base, length, bytes) * UCharArray::full(shift, 256, table) && tmp == 0 && shift1 == 0 */
  for (int i = 1; i < m1; i++)
    shift[hp_hash2(ne + i) /*@ where base = base, length = length, bytes = bytes, index = needleoff + i */] = i;
  shift1 = m1 - shift[hp_hash2(ne + m1) /*@ where base = base, length = length, bytes = bytes, index = needleoff + m1 */];
  shift[hp_hash2(ne + m1) /*@ where base = base, length = length, bytes = bytes, index = needleoff + m1 */] = m1;
  /*@ Inv Assert exists table position known, haystack == haystack@pre && needle == needle@pre &&
      hs_len == hs_len@pre && ne_len == ne_len@pre &&
      haystack == base + hayoff * sizeof(unsigned char) &&
      needle == base + needleoff * sizeof(unsigned char) &&
      0 < base && base + length <= UINT_MAX &&
      0 <= hayoff && 0 <= needleoff && 3 <= ne_len && ne_len <= 256 &&
      ne_len <= hs_len && hs_len <= known && known <= haylen && hp_cstring(bytes, hayoff, haylen) && hayoff + haylen < length && needleoff + ne_len <= length &&
      length <= 2147483647 && hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
      safeExec(ATrue, hp_search_from(bytes, hayoff, haylen, needleoff, ne_len, position), X) &&
      ne == needle && m1 == ne_len - 1 && 2 <= m1 && m1 <= 255 &&
      search_end == haystack + (known - ne_len) * sizeof(unsigned char) && hp_table_final(bytes, needleoff, ne_len, table, shift1) &&
      1 <= shift1 && shift1 <= m1 && hp_filter_offset(m1, offset) &&
      0 <= position && position <= known && hs == haystack + position * sizeof(unsigned char) &&
      hp_no_match_before(bytes, hayoff, haylen, needleoff, ne_len, position) && UCharArray::full(base, length, bytes) * UCharArray::full(shift, 256, table) && 0 <= tmp && tmp <= m1 */
  /* Restored from glibc strstr: extend the discovered frontier by at most
     2048 bytes. search_end is the latest known complete-window start. */
  while (1)
    {
      if (hs > search_end)
        {
          search_end += __strnlen(search_end + m1 + 1, 2048)
            /*@ where base = base, length = length, bytes = bytes,
                      hayoff = hayoff, haylen = haylen,
                      start = search_end + m1 + 1 - haystack */;
          if (hs > search_end)
            return (void *)0;
        }
  /*@ Assert exists table position known, haystack == haystack@pre && needle == needle@pre &&
      hs_len == hs_len@pre && ne_len == ne_len@pre &&
      haystack == base + hayoff * sizeof(unsigned char) &&
      needle == base + needleoff * sizeof(unsigned char) &&
      0 < base && base + length <= UINT_MAX &&
      0 <= hayoff && 0 <= needleoff && 3 <= ne_len && ne_len <= 256 &&
      ne_len <= hs_len && hs_len <= known && known <= haylen && hp_cstring(bytes, hayoff, haylen) && hayoff + haylen < length && needleoff + ne_len <= length &&
      length <= 2147483647 && hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
      safeExec(ATrue, hp_search_from(bytes, hayoff, haylen, needleoff, ne_len, position), X) &&
      ne == needle && m1 == ne_len - 1 && 2 <= m1 && m1 <= 255 &&
      search_end == haystack + (known - ne_len) * sizeof(unsigned char) && hp_table_final(bytes, needleoff, ne_len, table, shift1) &&
      1 <= shift1 && shift1 <= m1 && hp_filter_offset(m1, offset) &&
      0 <= position && position + ne_len <= known && hs == haystack + position * sizeof(unsigned char) &&
      hp_no_match_before(bytes, hayoff, haylen, needleoff, ne_len, position) && UCharArray::full(base, length, bytes) * UCharArray::full(shift, 256, table) && 0 <= tmp && tmp <= m1 */
      do
        {
          hs += m1;
          /*@ Assert exists table position known, haystack == haystack@pre && needle == needle@pre &&
      hs_len == hs_len@pre && ne_len == ne_len@pre &&
      haystack == base + hayoff * sizeof(unsigned char) &&
      needle == base + needleoff * sizeof(unsigned char) &&
      0 < base && base + length <= UINT_MAX &&
      0 <= hayoff && 0 <= needleoff && 3 <= ne_len && ne_len <= 256 &&
      ne_len <= hs_len && hs_len <= known && known <= haylen && hp_cstring(bytes, hayoff, haylen) && hayoff + haylen < length && needleoff + ne_len <= length &&
      length <= 2147483647 && hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
      safeExec(ATrue, hp_search_from(bytes, hayoff, haylen, needleoff, ne_len, position - m1), X) &&
      ne == needle && m1 == ne_len - 1 && 2 <= m1 && m1 <= 255 &&
      search_end == haystack + (known - ne_len) * sizeof(unsigned char) &&
              hp_table_final(bytes, needleoff, ne_len, table, shift1) &&
              1 <= shift1 && shift1 <= m1 && hp_filter_offset(m1, offset) &&
              m1 <= position && position < known &&
              hs == haystack + position * sizeof(unsigned char) &&
              hp_no_match_before(bytes, hayoff, haylen, needleoff, ne_len, position - m1) && UCharArray::full(base, length, bytes) * UCharArray::full(shift, 256, table) && 0 <= tmp && tmp <= m1 */
          tmp = shift[hp_hash2(hs) /*@ where base = base, length = length, bytes = bytes, index = hs - base */];
        }
      /*@ Inv Assert exists table position known, haystack == haystack@pre && needle == needle@pre &&
      hs_len == hs_len@pre && ne_len == ne_len@pre &&
      haystack == base + hayoff * sizeof(unsigned char) &&
      needle == base + needleoff * sizeof(unsigned char) &&
      0 < base && base + length <= UINT_MAX &&
      0 <= hayoff && 0 <= needleoff && 3 <= ne_len && ne_len <= 256 &&
      ne_len <= hs_len && hs_len <= known && known <= haylen && hp_cstring(bytes, hayoff, haylen) && hayoff + haylen < length && needleoff + ne_len <= length &&
      length <= 2147483647 && hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
      safeExec(ATrue, hp_search_from(bytes, hayoff, haylen, needleoff, ne_len, position - m1), X) &&
      ne == needle && m1 == ne_len - 1 && 2 <= m1 && m1 <= 255 &&
      search_end == haystack + (known - ne_len) * sizeof(unsigned char) && hp_table_final(bytes, needleoff, ne_len, table, shift1) &&
      1 <= shift1 && shift1 <= m1 && hp_filter_offset(m1, offset) &&
      m1 <= position && position < known && hs == haystack + position * sizeof(unsigned char) &&
      0 <= tmp && tmp <= m1 && tmp == table[hp_hash_at(bytes, hayoff + position)] &&
      hp_no_match_before(bytes, hayoff, haylen, needleoff, ne_len, position - m1) && UCharArray::full(base, length, bytes) * UCharArray::full(shift, 256, table) */
      while (tmp == 0 && hs <= search_end);
      hs -= tmp;
      /*@ Assert exists table position known, haystack == haystack@pre && needle == needle@pre &&
      hs_len == hs_len@pre && ne_len == ne_len@pre &&
      haystack == base + hayoff * sizeof(unsigned char) &&
      needle == base + needleoff * sizeof(unsigned char) &&
      0 < base && base + length <= UINT_MAX &&
      0 <= hayoff && 0 <= needleoff && 3 <= ne_len && ne_len <= 256 &&
      ne_len <= hs_len && hs_len <= known && known <= haylen && hp_cstring(bytes, hayoff, haylen) && hayoff + haylen < length && needleoff + ne_len <= length &&
      length <= 2147483647 && hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
      safeExec(ATrue, hp_search_from(bytes, hayoff, haylen, needleoff, ne_len, position), X) &&
      ne == needle && m1 == ne_len - 1 && 2 <= m1 && m1 <= 255 &&
      search_end == haystack + (known - ne_len) * sizeof(unsigned char) && hp_table_final(bytes, needleoff, ne_len, table, shift1) &&
      1 <= shift1 && shift1 <= m1 && hp_filter_offset(m1, offset) &&
      0 <= position && position <= known && hs == haystack + position * sizeof(unsigned char) &&
      hp_no_match_before(bytes, hayoff, haylen, needleoff, ne_len, position) && UCharArray::full(base, length, bytes) * UCharArray::full(shift, 256, table) &&
          0 <= tmp && tmp <= m1 &&
          (tmp == m1 => (position + ne_len <= known &&
            hp_hash_at(bytes, hayoff + position + m1) == hp_hash_at(bytes, needleoff + m1))) */
      if (tmp < m1)
        continue;
      if (m1 < 15 || memcmp(hs + offset, ne + offset, 8) /*@ where base = base, length = length, bytes = bytes, leftoff = hs - base + offset, rightoff = needleoff + offset */ == 0)
        {
          if (memcmp(hs, ne, m1) /*@ where base = base, length = length, bytes = bytes, leftoff = hs - base, rightoff = needleoff */ == 0)
            return (void *)hs;
          offset = (offset >= 8 ? offset : m1) - 8;
        }
      /*@ Assert exists table position known, haystack == haystack@pre && needle == needle@pre &&
      hs_len == hs_len@pre && ne_len == ne_len@pre &&
      haystack == base + hayoff * sizeof(unsigned char) &&
      needle == base + needleoff * sizeof(unsigned char) &&
      0 < base && base + length <= UINT_MAX &&
      0 <= hayoff && 0 <= needleoff && 3 <= ne_len && ne_len <= 256 &&
      ne_len <= hs_len && hs_len <= known && known <= haylen && hp_cstring(bytes, hayoff, haylen) && hayoff + haylen < length && needleoff + ne_len <= length &&
      length <= 2147483647 && hp_inputs(bytes, length, hayoff, haylen, needleoff, ne_len) &&
      safeExec(ATrue, hp_search_from(bytes, hayoff, haylen, needleoff, ne_len, position + shift1), X) &&
      ne == needle && m1 == ne_len - 1 && 2 <= m1 && m1 <= 255 &&
      search_end == haystack + (known - ne_len) * sizeof(unsigned char) && hp_table_final(bytes, needleoff, ne_len, table, shift1) &&
      1 <= shift1 && shift1 <= m1 && hp_filter_offset(m1, offset) &&
      0 <= position && position <= known && hs == haystack + position * sizeof(unsigned char) &&
      hp_no_match_before(bytes, hayoff, haylen, needleoff, ne_len, position) && UCharArray::full(base, length, bytes) * UCharArray::full(shift, 256, table) &&
          hp_no_match_before(bytes, hayoff, haylen, needleoff, ne_len, position + shift1) &&
          tmp == m1 && position + ne_len <= known */
      hs += shift1;
    }
}
