/* Object-bounded word-at-a-time strlen, Arch64 little endian.
 * Every memory access loads a real 64-bit word. The caller supplies an
 * aligned object and enough initialized capacity for the word containing
 * the first zero. No page permissions or bytes outside that object are used.
 * QCP proves its byte-memory model, not ISO C effective-type/provenance. */
#include "verification_stdlib.h"
#include "verification_list.h"
/*@ Import Coq Require Import SimpleC.EE.stdlib.glibc.strlen_word_lib */
/*@ Import Coq Import StrlenLittleEndian strlen_word_lib */
/*@ Extern Coq
 (sl_addr : Z -> Z)
 (ObjectString::store_string : Z -> Z -> list Z -> Assertion)
 (ObjectString::store_string_exact : Z -> list Z -> Assertion)
 (StrlenLittleEndian::valid_string : list Z -> Prop)
 (sl_suffix : Z -> Z -> Z)
 (sl_byte : Z -> Z -> Z)
 (sl_found : Z -> Z -> Z -> Prop)
 (sl_word_matches : Z -> list Z -> Z -> Prop)
 (sublist : {A} -> Z -> Z -> list A -> list A)
 (UCharArray::full : Z -> Z -> list Z -> Assertion)
 (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
*/

unsigned long long sl_load_word(const unsigned long long *p)
/*@ With s capacity bytes
 Require 0 <= s && s <= sl_addr(p) && sl_addr(p)+8 <= s+capacity &&
         s+capacity <= 18446744073709551615 && sl_addr(p)%8 == 0 &&
         UCharArray::full(s,capacity,bytes)
 Ensure sl_word_matches(__return,bytes,sl_addr(p)-s) &&
        0 <= __return && __return <= 18446744073709551615 &&
        UCharArray::full(s,capacity,bytes)
*/
{
 /* Convert exactly this object's eight selected byte cells to one word. */
 /*@ Assert exists word,
     p == p@pre && Zlength(bytes) == capacity && 0 <= s && s <= sl_addr(p) && sl_addr(p)+8 <= s+capacity &&
     s+capacity <= 18446744073709551615 && sl_addr(p)%8 == 0 &&
     0 <= word && word <= 18446744073709551615 &&
     sl_word_matches(word,bytes,sl_addr(p)-s) &&
     data_at(p,unsigned long long,word) *
     UCharArray::seg(s,0,sl_addr(p)-s,sublist(0,sl_addr(p)-s,bytes)) *
     UCharArray::seg(s,sl_addr(p)-s+8,capacity,sublist(sl_addr(p)-s+8,capacity,bytes)) */
 unsigned long long word = *p;
 return word;
}

/* Register-only search; 8 denotes absence of a zero byte. */
unsigned long long sl_first_zero(unsigned long long w, unsigned long long start)
/*@ Require 0 <= start && start < 8 && 0 <= w && w <= 18446744073709551615
 Ensure sl_found(w,start,__return)
*/
{
 unsigned long long i = 0;
 unsigned long long v = w;
 /*@ Inv Assert w == w@pre && start == start@pre &&
     0 <= start && start < 8 && 0 <= i && i <= start &&
     0 <= w && w <= 18446744073709551615 &&
     0 <= v && v <= 18446744073709551615 && v == sl_suffix(w,i) */
 while (i < start) {
   v = v / 256;
   i++;
 }
 /*@ Inv Assert w == w@pre && start == start@pre &&
     0 <= start && start < 8 && start <= i && i <= 8 &&
     0 <= w && w <= 18446744073709551615 &&
     0 <= v && v <= 18446744073709551615 && v == sl_suffix(w,i) &&
     (forall j, start <= j && j < i => sl_byte(w,j) != 0) */
 while (i < 8) {
   if (v % 256 == 0) return i;
   v = v / 256;
   i++;
 }
 return 8;
}

unsigned long long strlen_word(const unsigned char *s)
/*@ exact_spec <= capacity_spec
 With m
 Require 0 <= s && s%8 == 0 &&
         s+Zlength(m)+1 <= 18446744073709551615 &&
         8*(Zlength(m)/8+1) <= Zlength(m)+1 &&
         ObjectString::store_string_exact(s,m)
 Ensure __return == Zlength(m) && ObjectString::store_string_exact(s,m)
*/;

unsigned long long strlen_word(const unsigned char *s)
/*@ capacity_spec
 With capacity m
 Require 0 <= s && s%8 == 0 &&
         s+capacity <= 18446744073709551615 &&
         8*(Zlength(m)/8+1) <= capacity &&
         ObjectString::store_string(s,capacity,m)
 Ensure __return == Zlength(m) && ObjectString::store_string(s,capacity,m)
*/
{
 unsigned long long address = (unsigned long long)s;
 unsigned long long start = address % 8;
 unsigned long long p = address - start;
 /*@ Inv Assert exists tail,
     address == s && s == s@pre && start == 0 &&
     0 <= s && s%8 == 0 && s+capacity <= 18446744073709551615 &&
     8*(Zlength(m)/8+1) <= capacity &&
     s <= p && p <= s+Zlength(m) && p%8 == 0 &&
     StrlenLittleEndian::valid_string(m) &&
     UCharArray::full(s,capacity,app(m,cons(0,tail))) */
 while (1) {
   unsigned long long w = sl_load_word((const unsigned long long *)p);
   unsigned long long k = sl_first_zero(w,start);
   if (k < 8) return p+k-address;
   p += 8;
   start = 0;
 }
}
