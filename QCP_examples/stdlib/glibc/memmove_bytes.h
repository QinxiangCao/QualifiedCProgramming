/* Byte access helpers for the glibc memmove refinement.
 * Verification target: QCP Arch64 / LittleEndian. */
#include "verification_stdlib.h"
#include "verification_list.h"
/*@ Import Coq Require Import SimpleC.EE.stdlib.glibc.memmove_lib */
/*@ Extern Coq (mm_memory :: *) */
/*@ Extern Coq
 (mm_cells : Z -> Z -> mm_memory -> list (option Z))
 (mm_lookup : mm_memory -> Z -> option Z)
 (mm_write : mm_memory -> Z -> option Z -> mm_memory)
 (mm_in : Z -> Z -> Z -> Z -> Z -> Prop)
 (mm_separated : Z -> Z -> Z -> Z -> Prop)
 (mm_initialized : mm_memory -> Z -> Prop)
 (UCharArray::mixed_full : Z -> Z -> list (option Z) -> Assertion)
 (UCharArray::mixed_seg : Z -> Z -> Z -> list (option Z) -> Assertion)
 (UCharArray::mixed_missing_i : Z -> Z -> Z -> Z -> list (option Z) -> Assertion)
*/

unsigned char mm_load_byte(const unsigned char *p)
/*@ With b1 n1 b2 n2 (m : mm_memory)
 Require 0 <= n1 && 0 <= n2 && mm_in(p,b1,n1,b2,n2) &&
         mm_initialized(m,p) &&
         UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,m)) *
         UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,m))
 Ensure mm_lookup(m,p) == Some(__return) &&
        0 <= __return && __return <= 255 &&
        UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,m)) *
        UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,m))
*/;

void mm_store_byte(unsigned char *p, unsigned char value)
/*@ With b1 n1 b2 n2 (m : mm_memory)
 Require 0 <= n1 && 0 <= n2 && mm_in(p,b1,n1,b2,n2) &&
         mm_separated(b1,n1,b2,n2) &&
         UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,m)) *
         UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,m))
 Ensure UCharArray::mixed_full(b1,n1,mm_cells(b1,n1,mm_write(m,p,Some(value)))) *
        UCharArray::mixed_full(b2,n2,mm_cells(b2,n2,mm_write(m,p,Some(value))))
*/;
