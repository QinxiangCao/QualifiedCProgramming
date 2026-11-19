/* Verification adapter: no search work is added; this wrapper only calls the
 * already-verified dynamic Two-Way function under its exact existing contract.
 * The annotations split and restore the shared byte allocation. */
#include "verification_stdlib.h"
#include "verification_list.h"
/*@ Import Coq Require Import SimpleC.EE.stdlib.glibc.strstr_tw_bridge_lib */
/*@ Extern Coq
 (UCharArray::full : Z -> Z -> list Z -> Assertion)
 (sublist : {A} -> Z -> Z -> list A -> list A)
 (gs_inputs : list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (gs_tw_frame : Z -> Z -> list Z -> Z -> Z -> Z -> Z -> Assertion)
 (hp_result : list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (tw_nonzero_bytes : list Z -> Prop)
 (tw_terminator : Z -> Z -> Assertion)
 (match_post : list Z -> list Z -> option Z -> Prop)
 (uchar_ptr_option_repr : Z -> Z -> Z -> option Z)
*/
typedef unsigned long long size_t;
/* This is the high_level_spec proved in two-way_dynamic_RL.c. */
void *two_way_long_needle(const unsigned char *haystack, size_t haystack_len,
                          const unsigned char *needle, int needle_len)
/*@ With hay0 needle0 hn nn
 Require tw_nonzero_bytes(hay0) &&
         needle_len <= haystack_len && haystack_len <= hn && needle_len == nn &&
         32 < needle_len && needle_len <= hn && hn <= INT_MAX &&
         haystack > 0 && needle > 0 &&
         UCharArray::full(haystack,hn,hay0) * UCharArray::full(needle,needle_len,needle0) *
         tw_terminator(haystack,hn)
 Ensure exists ret,
         match_post(hay0,needle0,ret) &&
         uchar_ptr_option_repr(haystack,__return,sizeof(unsigned char)) == ret &&
         UCharArray::full(haystack,hn,hay0) * UCharArray::full(needle,needle_len,needle0) *
         tw_terminator(haystack,hn)
*/;

void *strstr_tw_bridge(const unsigned char *hs, size_t known,
                       const unsigned char *ne, int nl)
/*@ With base length bytes ho hl no
 Require hs == base+ho && ne == base+no && 0 < base && base+length <= UINT_MAX &&
         gs_inputs(bytes,length,ho,hl,no,nl) && 256 < nl && nl <= known && known <= hl &&
         UCharArray::full(base,length,bytes)
 Ensure hp_result(bytes,base,ho,hl,no,nl,__return) && UCharArray::full(base,length,bytes)
*/
{
 /*@ Assert nl == nl@pre && hs == base+ho && ne == base+no && 0 < base && base+length <= UINT_MAX &&
    gs_inputs(bytes,length,ho,hl,no,nl) && 256 < nl && nl <= known && known <= hl &&
    tw_nonzero_bytes(sublist(ho,ho+hl,bytes)) &&
    UCharArray::full(hs,hl,sublist(ho,ho+hl,bytes)) *
    UCharArray::full(ne,nl,sublist(no,no+nl,bytes)) * tw_terminator(hs,hl) *
    gs_tw_frame(base,length,bytes,ho,hl,no,nl) */
 void *r = two_way_long_needle(hs,known,ne,nl)
   /*@ where hay0 = sublist(ho,ho+hl,bytes), needle0 = sublist(no,no+nl,bytes), hn = hl, nn = nl */;
 /*@ Assert nl == nl@pre && hs == base+ho && ne == base+no &&
     nl <= known && known <= hl && hp_result(bytes,base,ho,hl,no,nl,r) && UCharArray::full(base,length,bytes) */
 return r;
}
