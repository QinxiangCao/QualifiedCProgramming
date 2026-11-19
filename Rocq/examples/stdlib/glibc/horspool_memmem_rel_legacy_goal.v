(* Historical VC statements retained only to reuse checked proofs.
   No automatic proofs or interface axioms are imported here. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.stdlib.glibc.horspool_memmem_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

(*----- Function hp_hash2 -----*)

Definition hp_hash2_safety_wit_1 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (256 <> 0) ”
.

Definition hp_hash2_safety_wit_2 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (3 <= 63) ” 
  &&  “ (0 <= 3) ”
.

Definition hp_hash2_safety_wit_3 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition hp_hash2_safety_wit_4 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
  **  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hp_hash2_safety_wit_5 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hp_hash2_safety_wit_6 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition hp_hash2_safety_wit_7 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition hp_hash2_entail_wit_1 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.full base length bytes )
|--
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
.

Definition hp_hash2_return_wit_1 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) ) = (hp_hash_at (bytes) (index))) ” 
  &&  “ (0 <= ((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) )) ” 
  &&  “ (((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) ) < 256) ”
  &&  (UCharArray.full base length bytes )
.

Definition hp_hash2_partial_solve_wit_1 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (((pointer_pre + (0 * sizeof(UCHAR) ) )) # UChar  |-> (Znth (0 - (0 - index ) ) bytes 0))
  **  (UCharArray.missing_i pointer_pre 0 (0 - index ) (length - index ) bytes )
.

Definition hp_hash2_partial_solve_wit_2 := 
forall (pointer_pre: Z) (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) ,
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= index) ” 
  &&  “ (index < length) ”
  &&  (((pointer_pre + ((-1) * sizeof(UCHAR) ) )) # UChar  |-> (Znth ((-1) - (0 - index ) ) bytes 0))
  **  (UCharArray.missing_i pointer_pre (-1) (0 - index ) (length - index ) bytes )
.

(*----- Function horspool_memmem_refinement -----*)

Definition horspool_memmem_refinement_safety_wit_1 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre < ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_2 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  ((( &( "shift1" ) )) # UInt64  |->_)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> ((haystack_pre + (hs_len_pre * sizeof(UCHAR) ) ) - (ne_len_pre * sizeof(UCHAR) ) ))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_3 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  ((( &( "tmp" ) )) # UInt64  |->_)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> ((haystack_pre + (hs_len_pre * sizeof(UCHAR) ) ) - (ne_len_pre * sizeof(UCHAR) ) ))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_4 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  ((( &( "m1" ) )) # UInt64  |->_)
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> ((haystack_pre + (hs_len_pre * sizeof(UCHAR) ) ) - (ne_len_pre * sizeof(UCHAR) ) ))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition horspool_memmem_refinement_safety_wit_5 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  ((( &( "offset" ) )) # UInt64  |->_)
  **  ((( &( "m1" ) )) # UInt64  |-> (unsigned_last_nbits ((ne_len_pre - 1 )) (64)))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> ((haystack_pre + (hs_len_pre * sizeof(UCHAR) ) ) - (ne_len_pre * sizeof(UCHAR) ) ))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_6 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "m1" ) )) # UInt64  |-> (unsigned_last_nbits ((ne_len_pre - 1 )) (64)))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> ((haystack_pre + (hs_len_pre * sizeof(UCHAR) ) ) - (ne_len_pre * sizeof(UCHAR) ) ))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_7 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "m1" ) )) # UInt64  |-> (unsigned_last_nbits ((ne_len_pre - 1 )) (64)))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> ((haystack_pre + (hs_len_pre * sizeof(UCHAR) ) ) - (ne_len_pre * sizeof(UCHAR) ) ))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_8 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "m1" ) )) # UInt64  |-> (unsigned_last_nbits ((ne_len_pre - 1 )) (64)))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> ((haystack_pre + (hs_len_pre * sizeof(UCHAR) ) ) - (ne_len_pre * sizeof(UCHAR) ) ))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition horspool_memmem_refinement_safety_wit_9 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (ne: Z) (m1: Z) (search_end: Z) (hs: Z) (offset: Z) (tmp: Z) (shift1: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 (repeat_Z (0) (256)) )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition horspool_memmem_refinement_safety_wit_10 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) ,
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) < m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full ( &( "shift" ) ) 256 (replace_Znth (retval) (i) (table)) )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition horspool_memmem_refinement_safety_wit_11 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (tmp: Z) (hs: Z) (offset: Z) (table: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position) ” 
  &&  “ (position < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position ))) table 0)) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ”
  &&  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_12 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (15 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 15) ”
.

Definition horspool_memmem_refinement_safety_wit_13 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition horspool_memmem_refinement_safety_wit_14 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_15 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) ,
  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_16 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_17 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition horspool_memmem_refinement_safety_wit_18 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (offset >= 8) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition horspool_memmem_refinement_safety_wit_19 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (offset < 8) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition horspool_memmem_refinement_safety_wit_20 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition horspool_memmem_refinement_safety_wit_21 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) ,
  “ (offset >= 8) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition horspool_memmem_refinement_safety_wit_22 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) ,
  “ (offset < 8) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition horspool_memmem_refinement_safety_wit_23 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (tmp: Z) (hs: Z) (offset: Z) (table: (@list Z)) (shift1: Z) (search_end: Z) (m1: Z) (ne: Z) (position: Z) ,
  “ (hs > search_end) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_entail_wit_1 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (retval: Z) ,
  “ (retval = (( &( "shift" ) ) + (0 * sizeof(UCHAR) ) )) ” 
  &&  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  (UCharArray.full ( &( "shift" ) ) 256 (repeat_Z (0) (256)) )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (needle_pre = needle_pre) ” 
  &&  “ ((unsigned_last_nbits ((ne_len_pre - 1 )) (64)) = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= (unsigned_last_nbits ((ne_len_pre - 1 )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((ne_len_pre - 1 )) (64)) <= 255) ” 
  &&  “ (((haystack_pre + (hs_len_pre * sizeof(UCHAR) ) ) - (ne_len_pre * sizeof(UCHAR) ) ) = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (haystack_pre = haystack_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 (repeat_Z (0) (256)) )
.

Definition horspool_memmem_refinement_entail_wit_2 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (ne: Z) (m1: Z) (search_end: Z) (hs: Z) (offset: Z) (tmp: Z) (shift1: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 (repeat_Z (0) (256)) )
|--
  EX (table: (@list Z)) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec 1 table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_3 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table_2: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) ,
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) < m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table_2 ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full ( &( "shift" ) ) 256 (replace_Znth (retval) (i) (table_2)) )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  EX (table: (@list Z)) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec (i + 1 ) table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_4 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < 256) ” 
  &&  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full ( &( "shift" ) ) 256 (replace_Znth (retval_2) (m1) (table)) )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  EX (table_2: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 (unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) ) ” 
  &&  “ (1 <= (unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64))) ” 
  &&  “ ((unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
.

Definition horspool_memmem_refinement_entail_wit_5 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (m1: Z) (ne: Z) (position_2: Z) ,
  “ (hs <= search_end) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position_2) ” 
  &&  “ (position_2 <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position) ” 
  &&  “ (position < hs_len_pre) ” 
  &&  “ ((hs + (m1 * sizeof(UCHAR) ) ) = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_6 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position_2: Z) ,
  “ (hs <= search_end) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position_2) ” 
  &&  “ (position_2 < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0)) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position) ” 
  &&  “ (position < hs_len_pre) ” 
  &&  “ ((hs + (m1 * sizeof(UCHAR) ) ) = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_7 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position_2: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((hs - base_low_level_spec )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position_2) ” 
  &&  “ (position_2 < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  EX (table_2: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position) ” 
  &&  “ (position < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= (Znth retval table 0)) ” 
  &&  “ ((Znth retval table 0) <= m1) ” 
  &&  “ ((Znth retval table 0) = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position ))) table_2 0)) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
.

Definition horspool_memmem_refinement_entail_wit_8_1 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position_2: Z) ,
  “ (hs > search_end) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position_2) ” 
  &&  “ (position_2 < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0)) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ ((hs - (tmp * sizeof(UCHAR) ) ) = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_8_2 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position_2: Z) ,
  “ (tmp <> 0) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position_2) ” 
  &&  “ (position_2 < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0)) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ ((hs - (tmp * sizeof(UCHAR) ) ) = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_9_1 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (offset >= 8) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position_2) ” 
  &&  “ (position_2 <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 (unsigned_last_nbits ((offset - 8 )) (64)) ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ” 
  &&  “ (tmp = m1) ” 
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_9_2 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (offset < 8) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position_2) ” 
  &&  “ (position_2 <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 (unsigned_last_nbits ((m1 - 8 )) (64)) ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ” 
  &&  “ (tmp = m1) ” 
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_9_3 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) ,
  “ (offset >= 8) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position_2) ” 
  &&  “ (position_2 <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 (unsigned_last_nbits ((offset - 8 )) (64)) ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ” 
  &&  “ (tmp = m1) ” 
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_9_4 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) ,
  “ (offset < 8) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position_2) ” 
  &&  “ (position_2 <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 (unsigned_last_nbits ((m1 - 8 )) (64)) ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ” 
  &&  “ (tmp = m1) ” 
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_9_5 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position_2) ” 
  &&  “ (position_2 <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ” 
  &&  “ (tmp = m1) ” 
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_10_1 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (tmp < m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position_2) ” 
  &&  “ (position_2 <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_entail_wit_10_2 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table_2: (@list Z)) (position_2: Z) (shift1: Z) (ne: Z) (m1: Z) (search_end: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 + shift1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position_2) ” 
  &&  “ (position_2 <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position_2 * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 ) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 + shift1 ) ) ” 
  &&  “ (tmp = m1) ” 
  &&  “ ((position_2 + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z))  (position: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ ((hs + (shift1 * sizeof(UCHAR) ) ) = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_return_wit_1 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (tmp: Z) (hs: Z) (offset: Z) (table: (@list Z)) (shift1: Z) (search_end: Z) (m1: Z) (ne: Z) (position: Z) ,
  “ (hs > search_end) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (0)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_return_wit_2 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval_2 ) ” 
  &&  “ (INT_MIN <= retval_2) ” 
  &&  “ (retval_2 <= INT_MAX) ” 
  &&  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (hs)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_return_wit_3 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs - base_low_level_spec ) needleoff_low_level_spec m1 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (hs)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_return_wit_4 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre < ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (0)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_1_pure := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "m1" ) )) # UInt64  |-> (unsigned_last_nbits ((ne_len_pre - 1 )) (64)))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> ((haystack_pre + (hs_len_pre * sizeof(UCHAR) ) ) - (ne_len_pre * sizeof(UCHAR) ) ))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ ((( &( "shift" ) ) + (0 * sizeof(UCHAR) ) ) = ( &( "shift" ) )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (256 = 256) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_1_aux := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) ,
  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ ((( &( "shift" ) ) + (0 * sizeof(UCHAR) ) ) = ( &( "shift" ) )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (256 = 256) ” 
  &&  “ (hs_len_pre >= ne_len_pre) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_1 := horspool_memmem_refinement_partial_solve_wit_1_pure -> horspool_memmem_refinement_partial_solve_wit_1_aux.

Definition horspool_memmem_refinement_partial_solve_wit_2_pure := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) ,
  “ ((unsigned_last_nbits (i) (64)) < m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
|--
  “ ((ne + (i * sizeof(UCHAR) ) ) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= (needleoff_low_level_spec + i )) ” 
  &&  “ ((needleoff_low_level_spec + i ) < length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_2_aux := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) ,
  “ ((unsigned_last_nbits (i) (64)) < m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ ((ne + (i * sizeof(UCHAR) ) ) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= (needleoff_low_level_spec + i )) ” 
  &&  “ ((needleoff_low_level_spec + i ) < length_low_level_spec) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) < m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_2 := horspool_memmem_refinement_partial_solve_wit_2_pure -> horspool_memmem_refinement_partial_solve_wit_2_aux.

Definition horspool_memmem_refinement_partial_solve_wit_3 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) ,
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) < m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) < m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (((( &( "shift" ) ) + (retval * sizeof(UCHAR) ) )) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "shift" ) ) retval 0 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_4_pure := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) ,
  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
|--
  “ ((ne + (m1 * sizeof(UCHAR) ) ) = (base_low_level_spec + ((needleoff_low_level_spec + m1 ) * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= (needleoff_low_level_spec + m1 )) ” 
  &&  “ ((needleoff_low_level_spec + m1 ) < length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_4_aux := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) ,
  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ ((ne + (m1 * sizeof(UCHAR) ) ) = (base_low_level_spec + ((needleoff_low_level_spec + m1 ) * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= (needleoff_low_level_spec + m1 )) ” 
  &&  “ ((needleoff_low_level_spec + m1 ) < length_low_level_spec) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_4 := horspool_memmem_refinement_partial_solve_wit_4_pure -> horspool_memmem_refinement_partial_solve_wit_4_aux.

Definition horspool_memmem_refinement_partial_solve_wit_5 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) ,
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (((( &( "shift" ) ) + (retval * sizeof(UCHAR) ) )) # UChar  |-> (Znth retval table 0))
  **  (UCharArray.missing_i ( &( "shift" ) ) retval 0 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_6_pure := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) ,
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
  **  ((( &( "shift1" ) )) # UInt64  |-> (unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)))
|--
  “ ((ne + (m1 * sizeof(UCHAR) ) ) = (base_low_level_spec + ((needleoff_low_level_spec + m1 ) * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= (needleoff_low_level_spec + m1 )) ” 
  &&  “ ((needleoff_low_level_spec + m1 ) < length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_6_aux := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) ,
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ ((ne + (m1 * sizeof(UCHAR) ) ) = (base_low_level_spec + ((needleoff_low_level_spec + m1 ) * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= (needleoff_low_level_spec + m1 )) ” 
  &&  “ ((needleoff_low_level_spec + m1 ) < length_low_level_spec) ” 
  &&  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_6 := horspool_memmem_refinement_partial_solve_wit_6_pure -> horspool_memmem_refinement_partial_solve_wit_6_aux.

Definition horspool_memmem_refinement_partial_solve_wit_7 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < 256) ” 
  &&  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (retval_2 = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < 256) ” 
  &&  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ ((unsigned_last_nbits (i) (64)) >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hs = haystack_pre) ” 
  &&  “ (offset = 0) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= m1) ” 
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ” 
  &&  “ (tmp = 0) ” 
  &&  “ (shift1 = 0) ”
  &&  (((( &( "shift" ) ) + (retval_2 * sizeof(UCHAR) ) )) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "shift" ) ) retval_2 0 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_8_pure := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position) ” 
  &&  “ (position < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (hs = (base_low_level_spec + ((hs - base_low_level_spec ) * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= (hs - base_low_level_spec )) ” 
  &&  “ ((hs - base_low_level_spec ) < length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_8_aux := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position) ” 
  &&  “ (position < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (hs = (base_low_level_spec + ((hs - base_low_level_spec ) * sizeof(UCHAR) ) )) ” 
  &&  “ (1 <= (hs - base_low_level_spec )) ” 
  &&  “ ((hs - base_low_level_spec ) < length_low_level_spec) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position) ” 
  &&  “ (position < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_8 := horspool_memmem_refinement_partial_solve_wit_8_pure -> horspool_memmem_refinement_partial_solve_wit_8_aux.

Definition horspool_memmem_refinement_partial_solve_wit_9 := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((hs - base_low_level_spec )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position) ” 
  &&  “ (position < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((hs - base_low_level_spec )))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 256) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (m1 <= position) ” 
  &&  “ (position < hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ”
  &&  (((( &( "shift" ) ) + (retval * sizeof(UCHAR) ) )) # UChar  |-> (Znth retval table 0))
  **  (UCharArray.missing_i ( &( "shift" ) ) retval 0 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_10_pure := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ ((hs + (offset * sizeof(UCHAR) ) ) = (base_low_level_spec + ((hs - base_low_level_spec ) + offset ) )) ” 
  &&  “ ((ne + (offset * sizeof(UCHAR) ) ) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (((needleoff_low_level_spec + offset ) + 8 ) <= length_low_level_spec) ” 
  &&  “ ((((hs - base_low_level_spec ) + offset ) + 8 ) <= length_low_level_spec) ” 
  &&  “ (0 <= (needleoff_low_level_spec + offset )) ” 
  &&  “ (0 <= ((hs - base_low_level_spec ) + offset )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_10_aux := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ ((hs + (offset * sizeof(UCHAR) ) ) = (base_low_level_spec + ((hs - base_low_level_spec ) + offset ) )) ” 
  &&  “ ((ne + (offset * sizeof(UCHAR) ) ) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (((needleoff_low_level_spec + offset ) + 8 ) <= length_low_level_spec) ” 
  &&  “ ((((hs - base_low_level_spec ) + offset ) + 8 ) <= length_low_level_spec) ” 
  &&  “ (0 <= (needleoff_low_level_spec + offset )) ” 
  &&  “ (0 <= ((hs - base_low_level_spec ) + offset )) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_10 := horspool_memmem_refinement_partial_solve_wit_10_pure -> horspool_memmem_refinement_partial_solve_wit_10_aux.

Definition horspool_memmem_refinement_partial_solve_wit_11_pure := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (hs = (base_low_level_spec + (hs - base_low_level_spec ) )) ” 
  &&  “ (ne = (base_low_level_spec + needleoff_low_level_spec )) ” 
  &&  “ (0 <= (hs - base_low_level_spec )) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= m1) ” 
  &&  “ (((hs - base_low_level_spec ) + m1 ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + m1 ) <= length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_11_aux := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (hs = (base_low_level_spec + (hs - base_low_level_spec ) )) ” 
  &&  “ (ne = (base_low_level_spec + needleoff_low_level_spec )) ” 
  &&  “ (0 <= (hs - base_low_level_spec )) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= m1) ” 
  &&  “ (((hs - base_low_level_spec ) + m1 ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + m1 ) <= length_low_level_spec) ” 
  &&  “ (retval = 0) ” 
  &&  “ (hp_memcmp_result bytes_low_level_spec ((hs - base_low_level_spec ) + offset ) (needleoff_low_level_spec + offset ) 8 retval ) ” 
  &&  “ (INT_MIN <= retval) ” 
  &&  “ (retval <= INT_MAX) ” 
  &&  “ (m1 >= 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_11 := horspool_memmem_refinement_partial_solve_wit_11_pure -> horspool_memmem_refinement_partial_solve_wit_11_aux.

Definition horspool_memmem_refinement_partial_solve_wit_12_pure := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  ((( &( "ne" ) )) # Ptr  |-> ne)
  **  ((( &( "m1" ) )) # UInt64  |-> m1)
  **  ((( &( "search_end" ) )) # Ptr  |-> search_end)
  **  ((( &( "shift1" ) )) # UInt64  |-> shift1)
  **  ((( &( "offset" ) )) # UInt64  |-> offset)
  **  ((( &( "hs" ) )) # Ptr  |-> hs)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  ((( &( "tmp" ) )) # UInt64  |-> tmp)
|--
  “ (hs = (base_low_level_spec + (hs - base_low_level_spec ) )) ” 
  &&  “ (ne = (base_low_level_spec + needleoff_low_level_spec )) ” 
  &&  “ (0 <= (hs - base_low_level_spec )) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= m1) ” 
  &&  “ (((hs - base_low_level_spec ) + m1 ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + m1 ) <= length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_12_aux := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) ,
  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (hs = (base_low_level_spec + (hs - base_low_level_spec ) )) ” 
  &&  “ (ne = (base_low_level_spec + needleoff_low_level_spec )) ” 
  &&  “ (0 <= (hs - base_low_level_spec )) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= m1) ” 
  &&  “ (((hs - base_low_level_spec ) + m1 ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + m1 ) <= length_low_level_spec) ” 
  &&  “ (m1 < 15) ” 
  &&  “ (tmp >= m1) ” 
  &&  “ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ (ne_len_pre <= hs_len_pre) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ” 
  &&  “ (ne = needle_pre) ” 
  &&  “ (m1 = (ne_len_pre - 1 )) ” 
  &&  “ (2 <= m1) ” 
  &&  “ (m1 <= 255) ” 
  &&  “ (search_end = (haystack_pre + ((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ” 
  &&  “ (1 <= shift1) ” 
  &&  “ (shift1 <= m1) ” 
  &&  “ (hp_filter_offset m1 offset ) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= hs_len_pre) ” 
  &&  “ (hs = (haystack_pre + (position * sizeof(UCHAR) ) )) ” 
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ” 
  &&  “ (0 <= tmp) ” 
  &&  “ (tmp <= m1) ” 
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_12 := horspool_memmem_refinement_partial_solve_wit_12_pure -> horspool_memmem_refinement_partial_solve_wit_12_aux.

Definition horspool_memmem_refinement_derive_high_level_spec_by_low_level_spec := 
forall (ne_len_pre: Z) (needle_pre: Z) (hs_len_pre: Z) (haystack_pre: Z) (needleoff_high_level_spec: Z) (hayoff_high_level_spec: Z) (bytes_high_level_spec: (@list Z)) (length_high_level_spec: Z) (base_high_level_spec: Z) ,
  “ (haystack_pre = (base_high_level_spec + (hayoff_high_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_high_level_spec + (needleoff_high_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_high_level_spec) ” 
  &&  “ ((base_high_level_spec + length_high_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_high_level_spec) ” 
  &&  “ (0 <= needleoff_high_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_high_level_spec + hs_len_pre ) <= length_high_level_spec) ” 
  &&  “ ((needleoff_high_level_spec + ne_len_pre ) <= length_high_level_spec) ” 
  &&  “ (length_high_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_high_level_spec length_high_level_spec hayoff_high_level_spec hs_len_pre needleoff_high_level_spec ne_len_pre ) ”
  &&  (UCharArray.full base_high_level_spec length_high_level_spec bytes_high_level_spec )
|--
EX (base_low_level_spec: Z) (length_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (hayoff_low_level_spec: Z) (needleoff_low_level_spec: Z) (X_low_level_spec: ((@option Z) -> (unit -> Prop))) ,
  (“ (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) )) ” 
  &&  “ (0 < base_low_level_spec) ” 
  &&  “ ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX) ” 
  &&  “ (0 <= hayoff_low_level_spec) ” 
  &&  “ (0 <= needleoff_low_level_spec) ” 
  &&  “ (0 <= hs_len_pre) ” 
  &&  “ (3 <= ne_len_pre) ” 
  &&  “ (ne_len_pre <= 256) ” 
  &&  “ ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec) ” 
  &&  “ ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec) ” 
  &&  “ (length_low_level_spec <= INT_MAX) ” 
  &&  “ (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre ) ” 
  &&  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec ))
  **
  ((EX retval_2,
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (retval_2)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec ))
  -*
  (EX retval,
  “ (hp_result bytes_high_level_spec base_high_level_spec hayoff_high_level_spec hs_len_pre needleoff_high_level_spec ne_len_pre retval ) ”
  &&  (UCharArray.full base_high_level_spec length_high_level_spec bytes_high_level_spec )))
.

