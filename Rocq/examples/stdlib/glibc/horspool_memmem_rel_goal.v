From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.EE.stdlib.glibc.horspool_memmem_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

(*----- Function hp_hash2 -----*)

Definition hp_hash2_safety_wit_1 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (256 <> 0) ”
.

Definition hp_hash2_safety_wit_2 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (3 <= 63) ”
  &&  “ (0 <= 3) ”
.

Definition hp_hash2_safety_wit_3 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition hp_hash2_safety_wit_4 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
  **  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition hp_hash2_safety_wit_5 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition hp_hash2_safety_wit_6 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (3 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 3) ”
.

Definition hp_hash2_safety_wit_7 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
  **  ((( &( "pointer" ) )) # Ptr  |-> pointer_pre)
|--
  “ (256 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 256) ”
.

Definition hp_hash2_entail_wit_1 :=
(
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.full base length bytes )
|--
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ”
  &&  “ (1 <= index) ”
  &&  “ (index < length) ”
  &&  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
) \/
(
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.full base length bytes )
|--
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
).

Definition hp_hash2_entail_wit_1_split_goal_spatial :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.full base length bytes )
|--
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
.

Definition hp_hash2_return_wit_1 :=
(
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) ) = (hp_hash_at (bytes) (index))) ”
  &&  “ (0 <= ((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) )) ”
  &&  “ (((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) ) < 256) ”
  &&  (UCharArray.full base length bytes )
) \/
(
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) ) < 256) ”
  &&  “ (0 <= ((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) )) ”
  &&  “ (((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) ) = (hp_hash_at (bytes) (index))) ”
  &&  (UCharArray.full base length bytes )
).

Definition hp_hash2_return_wit_1_split_goal_1 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) ) < 256) ”
.

Definition hp_hash2_return_wit_1_split_goal_2 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (0 <= ((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) )) ”
.

Definition hp_hash2_return_wit_1_split_goal_3 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (((unsigned_last_nbits (((Znth (0 - (0 - index ) ) bytes 0) - (unsigned_last_nbits ((Z.shiftl (Znth ((-1) - (0 - index ) ) bytes 0) 3)) (64)) )) (64)) % ( 256 ) ) = (hp_hash_at (bytes) (index))) ”
.

Definition hp_hash2_return_wit_1_split_goal_spatial :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  (UCharArray.full base length bytes )
.

Definition hp_hash2_partial_solve_wit_1 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ”
  &&  “ (1 <= index) ”
  &&  “ (index < length) ”
  &&  (((pointer_pre + (0 * sizeof(UCHAR)))) # UChar  |-> (Znth (0 - (0 - index ) ) bytes 0))
  **  (UCharArray.missing_i pointer_pre 0 (0 - index ) (length - index ) bytes )
.

Definition hp_hash2_partial_solve_wit_2 :=
forall (index: Z) (bytes: (@list Z)) (length: Z) (base: Z) (pointer_pre: Z) (PreH1 : (pointer_pre = (base + (index * sizeof(UCHAR) ) ))) (PreH2 : (1 <= index)) (PreH3 : (index < length)),
  (UCharArray.seg pointer_pre (0 - index ) (length - index ) bytes )
|--
  “ (pointer_pre = (base + (index * sizeof(UCHAR) ) )) ”
  &&  “ (1 <= index) ”
  &&  “ (index < length) ”
  &&  (((pointer_pre + ((-1) * sizeof(UCHAR)))) # UChar  |-> (Znth ((-1) - (0 - index ) ) bytes 0))
  **  (UCharArray.missing_i pointer_pre (-1) (0 - index ) (length - index ) bytes )
.

(*----- Function horspool_memmem_refinement -----*)

Definition horspool_memmem_refinement_safety_wit_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre < ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_2 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre >= ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  ((( &( "shift1" ) )) # UInt64  |->_)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> (haystack_pre + ((hs_len_pre + (-ne_len_pre) ) * sizeof(UCHAR))))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_3 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre >= ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  ((( &( "tmp" ) )) # UInt64  |->_)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> (haystack_pre + ((hs_len_pre + (-ne_len_pre) ) * sizeof(UCHAR))))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_4 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre >= ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  ((( &( "m1" ) )) # UInt64  |->_)
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> (haystack_pre + ((hs_len_pre + (-ne_len_pre) ) * sizeof(UCHAR))))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition horspool_memmem_refinement_safety_wit_5 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre >= ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  ((( &( "offset" ) )) # UInt64  |->_)
  **  ((( &( "m1" ) )) # UInt64  |-> (ne_len_pre - 1 ))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> (haystack_pre + ((hs_len_pre + (-ne_len_pre) ) * sizeof(UCHAR))))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_6 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre >= ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "m1" ) )) # UInt64  |-> (ne_len_pre - 1 ))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> (haystack_pre + ((hs_len_pre + (-ne_len_pre) ) * sizeof(UCHAR))))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_7 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre >= ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "m1" ) )) # UInt64  |-> (ne_len_pre - 1 ))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> (haystack_pre + ((hs_len_pre + (-ne_len_pre) ) * sizeof(UCHAR))))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition horspool_memmem_refinement_safety_wit_8 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre >= ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "m1" ) )) # UInt64  |-> (ne_len_pre - 1 ))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> (haystack_pre + ((hs_len_pre + (-ne_len_pre) ) * sizeof(UCHAR))))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (256 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 256) ”
.

Definition horspool_memmem_refinement_safety_wit_9 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (ne: Z) (m1: Z) (search_end: Z) (hs: Z) (offset: Z) (tmp: Z) (shift1: Z) (PreH1 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH2 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (0 < base_low_level_spec)) (PreH4 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH5 : (0 <= hayoff_low_level_spec)) (PreH6 : (0 <= needleoff_low_level_spec)) (PreH7 : (3 <= ne_len_pre)) (PreH8 : (ne_len_pre <= 256)) (PreH9 : (ne_len_pre <= hs_len_pre)) (PreH10 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH11 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH12 : (length_low_level_spec <= INT_MAX)) (PreH13 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH14 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH15 : (ne = needle_pre)) (PreH16 : (m1 = (ne_len_pre - 1 ))) (PreH17 : (2 <= m1)) (PreH18 : (m1 <= 255)) (PreH19 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH20 : (hs = haystack_pre)) (PreH21 : (offset = 0)) (PreH22 : (tmp = 0)) (PreH23 : (shift1 = 0)),
  ((( &( "i" ) )) # Int  |->_)
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (i < m1)) (PreH5 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (0 < base_low_level_spec)) (PreH8 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH9 : (0 <= hayoff_low_level_spec)) (PreH10 : (0 <= needleoff_low_level_spec)) (PreH11 : (3 <= ne_len_pre)) (PreH12 : (ne_len_pre <= 256)) (PreH13 : (ne_len_pre <= hs_len_pre)) (PreH14 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH15 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH16 : (length_low_level_spec <= INT_MAX)) (PreH17 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH18 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH19 : (ne = needle_pre)) (PreH20 : (m1 = (ne_len_pre - 1 ))) (PreH21 : (2 <= m1)) (PreH22 : (m1 <= 255)) (PreH23 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH24 : (hs = haystack_pre)) (PreH25 : (offset = 0)) (PreH26 : (1 <= i)) (PreH27 : (i <= m1)) (PreH28 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH29 : (tmp = 0)) (PreH30 : (shift1 = 0)),
  (UCharArray.full ( &( "shift" ) ) 256 (replace_Znth (retval) (i) (table)) )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position: Z) (PreH1 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH2 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (0 < base_low_level_spec)) (PreH4 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH5 : (0 <= hayoff_low_level_spec)) (PreH6 : (0 <= needleoff_low_level_spec)) (PreH7 : (3 <= ne_len_pre)) (PreH8 : (ne_len_pre <= 256)) (PreH9 : (ne_len_pre <= hs_len_pre)) (PreH10 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH11 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH12 : (length_low_level_spec <= INT_MAX)) (PreH13 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH14 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec )) (PreH15 : (ne = needle_pre)) (PreH16 : (m1 = (ne_len_pre - 1 ))) (PreH17 : (2 <= m1)) (PreH18 : (m1 <= 255)) (PreH19 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH20 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH21 : (1 <= shift1)) (PreH22 : (shift1 <= m1)) (PreH23 : (hp_filter_offset m1 offset )) (PreH24 : (m1 <= position)) (PreH25 : (position < hs_len_pre)) (PreH26 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH27 : (0 <= tmp)) (PreH28 : (tmp <= m1)) (PreH29 : (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position ))) table 0))) (PreH30 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) )),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp >= m1)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (0 <= position)) (PreH26 : (position <= hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)) (PreH31 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (m1 >= 15)) (PreH2 : (tmp >= m1)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : (ne_len_pre <= hs_len_pre)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH17 : (ne = needle_pre)) (PreH18 : (m1 = (ne_len_pre - 1 ))) (PreH19 : (2 <= m1)) (PreH20 : (m1 <= 255)) (PreH21 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH22 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH23 : (1 <= shift1)) (PreH24 : (shift1 <= m1)) (PreH25 : (hp_filter_offset m1 offset )) (PreH26 : (0 <= position)) (PreH27 : (position <= hs_len_pre)) (PreH28 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH29 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH30 : (0 <= tmp)) (PreH31 : (tmp <= m1)) (PreH32 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH2 : (INT_MIN <= retval)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (m1 >= 15)) (PreH5 : (tmp >= m1)) (PreH6 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (0 < base_low_level_spec)) (PreH9 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH10 : (0 <= hayoff_low_level_spec)) (PreH11 : (0 <= needleoff_low_level_spec)) (PreH12 : (3 <= ne_len_pre)) (PreH13 : (ne_len_pre <= 256)) (PreH14 : (ne_len_pre <= hs_len_pre)) (PreH15 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH16 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH17 : (length_low_level_spec <= INT_MAX)) (PreH18 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH19 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH20 : (ne = needle_pre)) (PreH21 : (m1 = (ne_len_pre - 1 ))) (PreH22 : (2 <= m1)) (PreH23 : (m1 <= 255)) (PreH24 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH25 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH26 : (1 <= shift1)) (PreH27 : (shift1 <= m1)) (PreH28 : (hp_filter_offset m1 offset )) (PreH29 : (0 <= position)) (PreH30 : (position <= hs_len_pre)) (PreH31 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH32 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH33 : (0 <= tmp)) (PreH34 : (tmp <= m1)) (PreH35 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH2 : (INT_MIN <= retval)) (PreH3 : (retval <= INT_MAX)) (PreH4 : (m1 < 15)) (PreH5 : (tmp >= m1)) (PreH6 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (0 < base_low_level_spec)) (PreH9 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH10 : (0 <= hayoff_low_level_spec)) (PreH11 : (0 <= needleoff_low_level_spec)) (PreH12 : (3 <= ne_len_pre)) (PreH13 : (ne_len_pre <= 256)) (PreH14 : (ne_len_pre <= hs_len_pre)) (PreH15 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH16 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH17 : (length_low_level_spec <= INT_MAX)) (PreH18 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH19 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH20 : (ne = needle_pre)) (PreH21 : (m1 = (ne_len_pre - 1 ))) (PreH22 : (2 <= m1)) (PreH23 : (m1 <= 255)) (PreH24 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH25 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH26 : (1 <= shift1)) (PreH27 : (shift1 <= m1)) (PreH28 : (hp_filter_offset m1 offset )) (PreH29 : (0 <= position)) (PreH30 : (position <= hs_len_pre)) (PreH31 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH32 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH33 : (0 <= tmp)) (PreH34 : (tmp <= m1)) (PreH35 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH2 : (INT_MIN <= retval_2)) (PreH3 : (retval_2 <= INT_MAX)) (PreH4 : (retval = 0)) (PreH5 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH6 : (INT_MIN <= retval)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (m1 >= 15)) (PreH9 : (tmp >= m1)) (PreH10 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH11 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH12 : (0 < base_low_level_spec)) (PreH13 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH14 : (0 <= hayoff_low_level_spec)) (PreH15 : (0 <= needleoff_low_level_spec)) (PreH16 : (3 <= ne_len_pre)) (PreH17 : (ne_len_pre <= 256)) (PreH18 : (ne_len_pre <= hs_len_pre)) (PreH19 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH20 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH21 : (length_low_level_spec <= INT_MAX)) (PreH22 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH23 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH24 : (ne = needle_pre)) (PreH25 : (m1 = (ne_len_pre - 1 ))) (PreH26 : (2 <= m1)) (PreH27 : (m1 <= 255)) (PreH28 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH29 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH30 : (1 <= shift1)) (PreH31 : (shift1 <= m1)) (PreH32 : (hp_filter_offset m1 offset )) (PreH33 : (0 <= position)) (PreH34 : (position <= hs_len_pre)) (PreH35 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH36 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH37 : (0 <= tmp)) (PreH38 : (tmp <= m1)) (PreH39 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH3 : (INT_MIN <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (m1 < 15)) (PreH6 : (tmp >= m1)) (PreH7 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (0 < base_low_level_spec)) (PreH10 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH11 : (0 <= hayoff_low_level_spec)) (PreH12 : (0 <= needleoff_low_level_spec)) (PreH13 : (3 <= ne_len_pre)) (PreH14 : (ne_len_pre <= 256)) (PreH15 : (ne_len_pre <= hs_len_pre)) (PreH16 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH17 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH18 : (length_low_level_spec <= INT_MAX)) (PreH19 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH20 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH21 : (ne = needle_pre)) (PreH22 : (m1 = (ne_len_pre - 1 ))) (PreH23 : (2 <= m1)) (PreH24 : (m1 <= 255)) (PreH25 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH26 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH27 : (1 <= shift1)) (PreH28 : (shift1 <= m1)) (PreH29 : (hp_filter_offset m1 offset )) (PreH30 : (0 <= position)) (PreH31 : (position <= hs_len_pre)) (PreH32 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH33 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH34 : (0 <= tmp)) (PreH35 : (tmp <= m1)) (PreH36 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (offset >= 8)) (PreH2 : (retval <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH4 : (INT_MIN <= retval)) (PreH5 : (retval <= INT_MAX)) (PreH6 : (m1 < 15)) (PreH7 : (tmp >= m1)) (PreH8 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH10 : (0 < base_low_level_spec)) (PreH11 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH12 : (0 <= hayoff_low_level_spec)) (PreH13 : (0 <= needleoff_low_level_spec)) (PreH14 : (3 <= ne_len_pre)) (PreH15 : (ne_len_pre <= 256)) (PreH16 : (ne_len_pre <= hs_len_pre)) (PreH17 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH18 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH19 : (length_low_level_spec <= INT_MAX)) (PreH20 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH21 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH22 : (ne = needle_pre)) (PreH23 : (m1 = (ne_len_pre - 1 ))) (PreH24 : (2 <= m1)) (PreH25 : (m1 <= 255)) (PreH26 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH28 : (1 <= shift1)) (PreH29 : (shift1 <= m1)) (PreH30 : (hp_filter_offset m1 offset )) (PreH31 : (0 <= position)) (PreH32 : (position <= hs_len_pre)) (PreH33 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH35 : (0 <= tmp)) (PreH36 : (tmp <= m1)) (PreH37 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (offset < 8)) (PreH2 : (retval <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH4 : (INT_MIN <= retval)) (PreH5 : (retval <= INT_MAX)) (PreH6 : (m1 < 15)) (PreH7 : (tmp >= m1)) (PreH8 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH10 : (0 < base_low_level_spec)) (PreH11 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH12 : (0 <= hayoff_low_level_spec)) (PreH13 : (0 <= needleoff_low_level_spec)) (PreH14 : (3 <= ne_len_pre)) (PreH15 : (ne_len_pre <= 256)) (PreH16 : (ne_len_pre <= hs_len_pre)) (PreH17 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH18 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH19 : (length_low_level_spec <= INT_MAX)) (PreH20 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH21 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH22 : (ne = needle_pre)) (PreH23 : (m1 = (ne_len_pre - 1 ))) (PreH24 : (2 <= m1)) (PreH25 : (m1 <= 255)) (PreH26 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH28 : (1 <= shift1)) (PreH29 : (shift1 <= m1)) (PreH30 : (hp_filter_offset m1 offset )) (PreH31 : (0 <= position)) (PreH32 : (position <= hs_len_pre)) (PreH33 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH35 : (0 <= tmp)) (PreH36 : (tmp <= m1)) (PreH37 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH3 : (INT_MIN <= retval_2)) (PreH4 : (retval_2 <= INT_MAX)) (PreH5 : (retval = 0)) (PreH6 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH7 : (INT_MIN <= retval)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (m1 >= 15)) (PreH10 : (tmp >= m1)) (PreH11 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH12 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (0 < base_low_level_spec)) (PreH14 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH15 : (0 <= hayoff_low_level_spec)) (PreH16 : (0 <= needleoff_low_level_spec)) (PreH17 : (3 <= ne_len_pre)) (PreH18 : (ne_len_pre <= 256)) (PreH19 : (ne_len_pre <= hs_len_pre)) (PreH20 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH21 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH22 : (length_low_level_spec <= INT_MAX)) (PreH23 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH24 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH25 : (ne = needle_pre)) (PreH26 : (m1 = (ne_len_pre - 1 ))) (PreH27 : (2 <= m1)) (PreH28 : (m1 <= 255)) (PreH29 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH30 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH31 : (1 <= shift1)) (PreH32 : (shift1 <= m1)) (PreH33 : (hp_filter_offset m1 offset )) (PreH34 : (0 <= position)) (PreH35 : (position <= hs_len_pre)) (PreH36 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH37 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH38 : (0 <= tmp)) (PreH39 : (tmp <= m1)) (PreH40 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (offset >= 8)) (PreH2 : (retval_2 <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH4 : (INT_MIN <= retval_2)) (PreH5 : (retval_2 <= INT_MAX)) (PreH6 : (retval = 0)) (PreH7 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH8 : (INT_MIN <= retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (m1 >= 15)) (PreH11 : (tmp >= m1)) (PreH12 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH14 : (0 < base_low_level_spec)) (PreH15 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH16 : (0 <= hayoff_low_level_spec)) (PreH17 : (0 <= needleoff_low_level_spec)) (PreH18 : (3 <= ne_len_pre)) (PreH19 : (ne_len_pre <= 256)) (PreH20 : (ne_len_pre <= hs_len_pre)) (PreH21 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH22 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH23 : (length_low_level_spec <= INT_MAX)) (PreH24 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH25 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH26 : (ne = needle_pre)) (PreH27 : (m1 = (ne_len_pre - 1 ))) (PreH28 : (2 <= m1)) (PreH29 : (m1 <= 255)) (PreH30 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH31 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH32 : (1 <= shift1)) (PreH33 : (shift1 <= m1)) (PreH34 : (hp_filter_offset m1 offset )) (PreH35 : (0 <= position)) (PreH36 : (position <= hs_len_pre)) (PreH37 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH39 : (0 <= tmp)) (PreH40 : (tmp <= m1)) (PreH41 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (offset < 8)) (PreH2 : (retval_2 <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH4 : (INT_MIN <= retval_2)) (PreH5 : (retval_2 <= INT_MAX)) (PreH6 : (retval = 0)) (PreH7 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH8 : (INT_MIN <= retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (m1 >= 15)) (PreH11 : (tmp >= m1)) (PreH12 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH14 : (0 < base_low_level_spec)) (PreH15 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH16 : (0 <= hayoff_low_level_spec)) (PreH17 : (0 <= needleoff_low_level_spec)) (PreH18 : (3 <= ne_len_pre)) (PreH19 : (ne_len_pre <= 256)) (PreH20 : (ne_len_pre <= hs_len_pre)) (PreH21 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH22 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH23 : (length_low_level_spec <= INT_MAX)) (PreH24 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH25 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH26 : (ne = needle_pre)) (PreH27 : (m1 = (ne_len_pre - 1 ))) (PreH28 : (2 <= m1)) (PreH29 : (m1 <= 255)) (PreH30 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH31 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH32 : (1 <= shift1)) (PreH33 : (shift1 <= m1)) (PreH34 : (hp_filter_offset m1 offset )) (PreH35 : (0 <= position)) (PreH36 : (position <= hs_len_pre)) (PreH37 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH39 : (0 <= tmp)) (PreH40 : (tmp <= m1)) (PreH41 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table: (@list Z)) (shift1: Z) (search_end: Z) (m1: Z) (ne: Z) (position: Z) (PreH1 : (hs > search_end)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (0 <= position)) (PreH26 : (position <= hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (retval: Z) (PreH1 : (retval = (( &( "shift" ) ) + (0 * sizeof(UCHAR))))) (PreH2 : (hs_len_pre >= ne_len_pre)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (0 <= hs_len_pre)) (PreH10 : (3 <= ne_len_pre)) (PreH11 : (ne_len_pre <= 256)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  (UCharArray.full ( &( "shift" ) ) 256 (repeat_Z (0) (256)) )
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
  &&  “ ((ne_len_pre - 1 ) = (ne_len_pre - 1 )) ”
  &&  “ (2 <= (ne_len_pre - 1 )) ”
  &&  “ ((ne_len_pre - 1 ) <= 255) ”
  &&  “ ((haystack_pre + ((hs_len_pre + (-ne_len_pre) ) * sizeof(UCHAR))) = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (haystack_pre = haystack_pre) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  “ (0 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 (repeat_Z (0) (256)) )
.

Definition horspool_memmem_refinement_entail_wit_2 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (ne: Z) (m1: Z) (search_end: Z) (hs: Z) (offset: Z) (tmp: Z) (shift1: Z) (PreH1 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH2 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (0 < base_low_level_spec)) (PreH4 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH5 : (0 <= hayoff_low_level_spec)) (PreH6 : (0 <= needleoff_low_level_spec)) (PreH7 : (3 <= ne_len_pre)) (PreH8 : (ne_len_pre <= 256)) (PreH9 : (ne_len_pre <= hs_len_pre)) (PreH10 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH11 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH12 : (length_low_level_spec <= INT_MAX)) (PreH13 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH14 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH15 : (ne = needle_pre)) (PreH16 : (m1 = (ne_len_pre - 1 ))) (PreH17 : (2 <= m1)) (PreH18 : (m1 <= 255)) (PreH19 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH20 : (hs = haystack_pre)) (PreH21 : (offset = 0)) (PreH22 : (tmp = 0)) (PreH23 : (shift1 = 0)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 (repeat_Z (0) (256)) )
|--
  EX (table: (@list Z)),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hs = haystack_pre) ”
  &&  “ (offset = 0) ”
  &&  “ (1 <= 1) ”
  &&  “ (1 <= m1) ”
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec 1 table ) ”
  &&  “ (tmp = 0) ”
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (ne: Z) (m1: Z) (search_end: Z) (hs: Z) (offset: Z) (tmp: Z) (shift1: Z) (PreH1 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH2 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (0 < base_low_level_spec)) (PreH4 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH5 : (0 <= hayoff_low_level_spec)) (PreH6 : (0 <= needleoff_low_level_spec)) (PreH7 : (3 <= ne_len_pre)) (PreH8 : (ne_len_pre <= 256)) (PreH9 : (ne_len_pre <= hs_len_pre)) (PreH10 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH11 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH12 : (length_low_level_spec <= INT_MAX)) (PreH13 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH14 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH15 : (ne = needle_pre)) (PreH16 : (m1 = (ne_len_pre - 1 ))) (PreH17 : (2 <= m1)) (PreH18 : (m1 <= 255)) (PreH19 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH20 : (hs = haystack_pre)) (PreH21 : (offset = 0)) (PreH22 : (tmp = 0)) (PreH23 : (shift1 = 0)),
  TT && emp 
|--
  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec 1 (repeat_Z (0) (256)) ) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_2_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (ne: Z) (m1: Z) (search_end: Z) (hs: Z) (offset: Z) (tmp: Z) (shift1: Z) (PreH1 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH2 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (0 < base_low_level_spec)) (PreH4 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH5 : (0 <= hayoff_low_level_spec)) (PreH6 : (0 <= needleoff_low_level_spec)) (PreH7 : (3 <= ne_len_pre)) (PreH8 : (ne_len_pre <= 256)) (PreH9 : (ne_len_pre <= hs_len_pre)) (PreH10 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH11 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH12 : (length_low_level_spec <= INT_MAX)) (PreH13 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH14 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH15 : (ne = needle_pre)) (PreH16 : (m1 = (ne_len_pre - 1 ))) (PreH17 : (2 <= m1)) (PreH18 : (m1 <= 255)) (PreH19 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH20 : (hs = haystack_pre)) (PreH21 : (offset = 0)) (PreH22 : (tmp = 0)) (PreH23 : (shift1 = 0)),
  (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec 1 (repeat_Z (0) (256)) )
.

Definition horspool_memmem_refinement_entail_wit_3 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table_2: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (i < m1)) (PreH5 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (0 < base_low_level_spec)) (PreH8 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH9 : (0 <= hayoff_low_level_spec)) (PreH10 : (0 <= needleoff_low_level_spec)) (PreH11 : (3 <= ne_len_pre)) (PreH12 : (ne_len_pre <= 256)) (PreH13 : (ne_len_pre <= hs_len_pre)) (PreH14 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH15 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH16 : (length_low_level_spec <= INT_MAX)) (PreH17 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH18 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH19 : (ne = needle_pre)) (PreH20 : (m1 = (ne_len_pre - 1 ))) (PreH21 : (2 <= m1)) (PreH22 : (m1 <= 255)) (PreH23 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH24 : (hs = haystack_pre)) (PreH25 : (offset = 0)) (PreH26 : (1 <= i)) (PreH27 : (i <= m1)) (PreH28 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table_2 )) (PreH29 : (tmp = 0)) (PreH30 : (shift1 = 0)),
  (UCharArray.full ( &( "shift" ) ) 256 (replace_Znth (retval) (i) (table_2)) )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  EX (table: (@list Z)),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hs = haystack_pre) ”
  &&  “ (offset = 0) ”
  &&  “ (1 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= m1) ”
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec (i + 1 ) table ) ”
  &&  “ (tmp = 0) ”
  &&  “ (shift1 = 0) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table_2: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (i < m1)) (PreH5 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (0 < base_low_level_spec)) (PreH8 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH9 : (0 <= hayoff_low_level_spec)) (PreH10 : (0 <= needleoff_low_level_spec)) (PreH11 : (3 <= ne_len_pre)) (PreH12 : (ne_len_pre <= 256)) (PreH13 : (ne_len_pre <= hs_len_pre)) (PreH14 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH15 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH16 : (length_low_level_spec <= INT_MAX)) (PreH17 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH18 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH19 : (ne = needle_pre)) (PreH20 : (m1 = (ne_len_pre - 1 ))) (PreH21 : (2 <= m1)) (PreH22 : (m1 <= 255)) (PreH23 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH24 : (hs = haystack_pre)) (PreH25 : (offset = 0)) (PreH26 : (1 <= i)) (PreH27 : (i <= m1)) (PreH28 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table_2 )) (PreH29 : (tmp = 0)) (PreH30 : (shift1 = 0)),
  TT && emp 
|--
  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec (i + 1 ) (replace_Znth (retval) (i) (table_2)) ) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_3_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table_2: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (i < m1)) (PreH5 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (0 < base_low_level_spec)) (PreH8 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH9 : (0 <= hayoff_low_level_spec)) (PreH10 : (0 <= needleoff_low_level_spec)) (PreH11 : (3 <= ne_len_pre)) (PreH12 : (ne_len_pre <= 256)) (PreH13 : (ne_len_pre <= hs_len_pre)) (PreH14 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH15 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH16 : (length_low_level_spec <= INT_MAX)) (PreH17 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH18 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH19 : (ne = needle_pre)) (PreH20 : (m1 = (ne_len_pre - 1 ))) (PreH21 : (2 <= m1)) (PreH22 : (m1 <= 255)) (PreH23 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH24 : (hs = haystack_pre)) (PreH25 : (offset = 0)) (PreH26 : (1 <= i)) (PreH27 : (i <= m1)) (PreH28 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table_2 )) (PreH29 : (tmp = 0)) (PreH30 : (shift1 = 0)),
  (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec (i + 1 ) (replace_Znth (retval) (i) (table_2)) )
.

Definition horspool_memmem_refinement_entail_wit_4 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (i >= m1)) (PreH8 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH10 : (0 < base_low_level_spec)) (PreH11 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH12 : (0 <= hayoff_low_level_spec)) (PreH13 : (0 <= needleoff_low_level_spec)) (PreH14 : (3 <= ne_len_pre)) (PreH15 : (ne_len_pre <= 256)) (PreH16 : (ne_len_pre <= hs_len_pre)) (PreH17 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH18 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH19 : (length_low_level_spec <= INT_MAX)) (PreH20 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH21 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH22 : (ne = needle_pre)) (PreH23 : (m1 = (ne_len_pre - 1 ))) (PreH24 : (2 <= m1)) (PreH25 : (m1 <= 255)) (PreH26 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH27 : (hs = haystack_pre)) (PreH28 : (offset = 0)) (PreH29 : (1 <= i)) (PreH30 : (i <= m1)) (PreH31 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH32 : (tmp = 0)) (PreH33 : (shift1 = 0)),
  (UCharArray.full ( &( "shift" ) ) 256 (replace_Znth (retval_2) (m1) (table)) )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  EX (table_2: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 (unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) ) ”
  &&  “ (1 <= (unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64))) ”
  &&  “ ((unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (i >= m1)) (PreH8 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH10 : (0 < base_low_level_spec)) (PreH11 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH12 : (0 <= hayoff_low_level_spec)) (PreH13 : (0 <= needleoff_low_level_spec)) (PreH14 : (3 <= ne_len_pre)) (PreH15 : (ne_len_pre <= 256)) (PreH16 : (ne_len_pre <= hs_len_pre)) (PreH17 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH18 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH19 : (length_low_level_spec <= INT_MAX)) (PreH20 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH21 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH22 : (ne = needle_pre)) (PreH23 : (m1 = (ne_len_pre - 1 ))) (PreH24 : (2 <= m1)) (PreH25 : (m1 <= 255)) (PreH26 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH27 : (hs = haystack_pre)) (PreH28 : (offset = 0)) (PreH29 : (1 <= i)) (PreH30 : (i <= m1)) (PreH31 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH32 : (tmp = 0)) (PreH33 : (shift1 = 0)),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre (replace_Znth ((hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + (ne_len_pre - 1 ) )))) ((ne_len_pre - 1 )) (table)) (unsigned_last_nbits (((ne_len_pre - 1 ) - (unsigned_last_nbits ((Znth (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + (ne_len_pre - 1 ) ))) table 0)) (64)) )) (64)) ) ”
  &&  “ (1 <= (unsigned_last_nbits (((ne_len_pre - 1 ) - (unsigned_last_nbits ((Znth (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + (ne_len_pre - 1 ) ))) table 0)) (64)) )) (64))) ”
  &&  “ ((unsigned_last_nbits (((ne_len_pre - 1 ) - (unsigned_last_nbits ((Znth (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + (ne_len_pre - 1 ) ))) table 0)) (64)) )) (64)) <= (ne_len_pre - 1 )) ”
  &&  “ (hp_filter_offset (ne_len_pre - 1 ) 0 ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (haystack_pre = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (ne_len_pre - 1 )) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_5 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (m1: Z) (ne: Z) (position_2: Z) (PreH1 : (hs <= search_end)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (0 <= position_2)) (PreH26 : (position_2 <= hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (m1 <= position) ”
  &&  “ (position < hs_len_pre) ”
  &&  “ ((hs + (m1 * sizeof(UCHAR))) = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (m1: Z) (ne: Z) (position_2: Z) (PreH1 : (hs <= search_end)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (0 <= position_2)) (PreH26 : (position_2 <= hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - (ne_len_pre - 1 ) ))) X_low_level_spec ) ”
  &&  “ ((ne_len_pre - 1 ) <= position) ”
  &&  “ (position < hs_len_pre) ”
  &&  “ (((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - (ne_len_pre - 1 ) ) ) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_6 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position_2: Z) (PreH1 : (hs <= search_end)) (PreH2 : (tmp = 0)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : (ne_len_pre <= hs_len_pre)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec )) (PreH17 : (ne = needle_pre)) (PreH18 : (m1 = (ne_len_pre - 1 ))) (PreH19 : (2 <= m1)) (PreH20 : (m1 <= 255)) (PreH21 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH22 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH23 : (1 <= shift1)) (PreH24 : (shift1 <= m1)) (PreH25 : (hp_filter_offset m1 offset )) (PreH26 : (m1 <= position_2)) (PreH27 : (position_2 < hs_len_pre)) (PreH28 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)) (PreH31 : (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0))) (PreH32 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) )),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (m1 <= position) ”
  &&  “ (position < hs_len_pre) ”
  &&  “ ((hs + (m1 * sizeof(UCHAR))) = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position_2: Z) (PreH1 : (hs <= search_end)) (PreH2 : (tmp = 0)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : (ne_len_pre <= hs_len_pre)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec )) (PreH17 : (ne = needle_pre)) (PreH18 : (m1 = (ne_len_pre - 1 ))) (PreH19 : (2 <= m1)) (PreH20 : (m1 <= 255)) (PreH21 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH22 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH23 : (1 <= shift1)) (PreH24 : (shift1 <= m1)) (PreH25 : (hp_filter_offset m1 offset )) (PreH26 : (m1 <= position_2)) (PreH27 : (position_2 < hs_len_pre)) (PreH28 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)) (PreH31 : (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0))) (PreH32 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) )),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - (ne_len_pre - 1 ) ))) X_low_level_spec ) ”
  &&  “ ((ne_len_pre - 1 ) <= position) ”
  &&  “ (position < hs_len_pre) ”
  &&  “ (((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - (ne_len_pre - 1 ) ) ) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_7 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position_2: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((hs + ((-base_low_level_spec) * sizeof(UCHAR))))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (0 < base_low_level_spec)) (PreH7 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH8 : (0 <= hayoff_low_level_spec)) (PreH9 : (0 <= needleoff_low_level_spec)) (PreH10 : (3 <= ne_len_pre)) (PreH11 : (ne_len_pre <= 256)) (PreH12 : (ne_len_pre <= hs_len_pre)) (PreH13 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH14 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH15 : (length_low_level_spec <= INT_MAX)) (PreH16 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH17 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec )) (PreH18 : (ne = needle_pre)) (PreH19 : (m1 = (ne_len_pre - 1 ))) (PreH20 : (2 <= m1)) (PreH21 : (m1 <= 255)) (PreH22 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH23 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH24 : (1 <= shift1)) (PreH25 : (shift1 <= m1)) (PreH26 : (hp_filter_offset m1 offset )) (PreH27 : (m1 <= position_2)) (PreH28 : (position_2 < hs_len_pre)) (PreH29 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH30 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) )) (PreH31 : (0 <= tmp)) (PreH32 : (tmp <= m1)),
  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  EX (table_2: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (m1 <= position) ”
  &&  “ (position < hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (0 <= (Znth retval table 0)) ”
  &&  “ ((Znth retval table 0) <= m1) ”
  &&  “ ((Znth retval table 0) = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position ))) table_2 0)) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position_2: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((hs + ((-base_low_level_spec) * sizeof(UCHAR))))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (0 < base_low_level_spec)) (PreH7 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH8 : (0 <= hayoff_low_level_spec)) (PreH9 : (0 <= needleoff_low_level_spec)) (PreH10 : (3 <= ne_len_pre)) (PreH11 : (ne_len_pre <= 256)) (PreH12 : (ne_len_pre <= hs_len_pre)) (PreH13 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH14 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH15 : (length_low_level_spec <= INT_MAX)) (PreH16 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH17 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec )) (PreH18 : (ne = needle_pre)) (PreH19 : (m1 = (ne_len_pre - 1 ))) (PreH20 : (2 <= m1)) (PreH21 : (m1 <= 255)) (PreH22 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH23 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH24 : (1 <= shift1)) (PreH25 : (shift1 <= m1)) (PreH26 : (hp_filter_offset m1 offset )) (PreH27 : (m1 <= position_2)) (PreH28 : (position_2 < hs_len_pre)) (PreH29 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH30 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) )) (PreH31 : (0 <= tmp)) (PreH32 : (tmp <= m1)),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - (ne_len_pre - 1 ) ))) X_low_level_spec ) ”
  &&  “ ((ne_len_pre - 1 ) <= position) ”
  &&  “ (position < hs_len_pre) ”
  &&  “ ((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (0 <= (Znth (hp_hash_at (bytes_low_level_spec) (((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) + ((-base_low_level_spec) * sizeof(UCHAR))))) table 0)) ”
  &&  “ ((Znth (hp_hash_at (bytes_low_level_spec) (((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) + ((-base_low_level_spec) * sizeof(UCHAR))))) table 0) <= (ne_len_pre - 1 )) ”
  &&  “ ((Znth (hp_hash_at (bytes_low_level_spec) (((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) + ((-base_low_level_spec) * sizeof(UCHAR))))) table 0) = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position ))) table 0)) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - (ne_len_pre - 1 ) ) ) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_8_1 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position_2: Z) (PreH1 : (tmp <> 0)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (m1 <= position_2)) (PreH26 : (position_2 < hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH28 : (0 <= tmp)) (PreH29 : (tmp <= m1)) (PreH30 : (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0))) (PreH31 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) )),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ ((hs + ((-tmp) * sizeof(UCHAR))) = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position_2: Z) (PreH1 : (tmp <> 0)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (m1 <= position_2)) (PreH26 : (position_2 < hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH28 : (0 <= tmp)) (PreH29 : (tmp <= m1)) (PreH30 : (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0))) (PreH31 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) )),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) + ((-(Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0)) * sizeof(UCHAR))) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (((Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0) = (ne_len_pre - 1 )) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + (ne_len_pre - 1 ) ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + (ne_len_pre - 1 ) )))))) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_8_2 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position_2: Z) (PreH1 : (hs > search_end)) (PreH2 : (tmp = 0)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : (ne_len_pre <= hs_len_pre)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec )) (PreH17 : (ne = needle_pre)) (PreH18 : (m1 = (ne_len_pre - 1 ))) (PreH19 : (2 <= m1)) (PreH20 : (m1 <= 255)) (PreH21 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH22 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH23 : (1 <= shift1)) (PreH24 : (shift1 <= m1)) (PreH25 : (hp_filter_offset m1 offset )) (PreH26 : (m1 <= position_2)) (PreH27 : (position_2 < hs_len_pre)) (PreH28 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)) (PreH31 : (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0))) (PreH32 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) )),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ ((hs + ((-tmp) * sizeof(UCHAR))) = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table_2: (@list Z)) (shift1: Z) (search_end: Z) (ne: Z) (m1: Z) (position_2: Z) (PreH1 : (hs > search_end)) (PreH2 : (tmp = 0)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : (ne_len_pre <= hs_len_pre)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 - m1 ))) X_low_level_spec )) (PreH17 : (ne = needle_pre)) (PreH18 : (m1 = (ne_len_pre - 1 ))) (PreH19 : (2 <= m1)) (PreH20 : (m1 <= 255)) (PreH21 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH22 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH23 : (1 <= shift1)) (PreH24 : (shift1 <= m1)) (PreH25 : (hp_filter_offset m1 offset )) (PreH26 : (m1 <= position_2)) (PreH27 : (position_2 < hs_len_pre)) (PreH28 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)) (PreH31 : (tmp = (Znth (hp_hash_at (bytes_low_level_spec) ((hayoff_low_level_spec + position_2 ))) table_2 0))) (PreH32 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 - m1 ) )),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) + ((-0) * sizeof(UCHAR))) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ ((0 = (ne_len_pre - 1 )) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + (ne_len_pre - 1 ) ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + (ne_len_pre - 1 ) )))))) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_9_1 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (offset >= 8)) (PreH2 : (retval <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH4 : (INT_MIN <= retval)) (PreH5 : (retval <= INT_MAX)) (PreH6 : (m1 < 15)) (PreH7 : (tmp >= m1)) (PreH8 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH10 : (0 < base_low_level_spec)) (PreH11 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH12 : (0 <= hayoff_low_level_spec)) (PreH13 : (0 <= needleoff_low_level_spec)) (PreH14 : (3 <= ne_len_pre)) (PreH15 : (ne_len_pre <= 256)) (PreH16 : (ne_len_pre <= hs_len_pre)) (PreH17 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH18 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH19 : (length_low_level_spec <= INT_MAX)) (PreH20 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH21 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH22 : (ne = needle_pre)) (PreH23 : (m1 = (ne_len_pre - 1 ))) (PreH24 : (2 <= m1)) (PreH25 : (m1 <= 255)) (PreH26 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH28 : (1 <= shift1)) (PreH29 : (shift1 <= m1)) (PreH30 : (hp_filter_offset m1 offset )) (PreH31 : (0 <= position_2)) (PreH32 : (position_2 <= hs_len_pre)) (PreH33 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH35 : (0 <= tmp)) (PreH36 : (tmp <= m1)) (PreH37 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 (offset - 8 ) ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = m1) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (offset >= 8)) (PreH2 : (retval <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH4 : (INT_MIN <= retval)) (PreH5 : (retval <= INT_MAX)) (PreH6 : (m1 < 15)) (PreH7 : (tmp >= m1)) (PreH8 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH10 : (0 < base_low_level_spec)) (PreH11 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH12 : (0 <= hayoff_low_level_spec)) (PreH13 : (0 <= needleoff_low_level_spec)) (PreH14 : (3 <= ne_len_pre)) (PreH15 : (ne_len_pre <= 256)) (PreH16 : (ne_len_pre <= hs_len_pre)) (PreH17 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH18 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH19 : (length_low_level_spec <= INT_MAX)) (PreH20 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH21 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH22 : (ne = needle_pre)) (PreH23 : (m1 = (ne_len_pre - 1 ))) (PreH24 : (2 <= m1)) (PreH25 : (m1 <= 255)) (PreH26 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH28 : (1 <= shift1)) (PreH29 : (shift1 <= m1)) (PreH30 : (hp_filter_offset m1 offset )) (PreH31 : (0 <= position_2)) (PreH32 : (position_2 <= hs_len_pre)) (PreH33 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH35 : (0 <= tmp)) (PreH36 : (tmp <= m1)) (PreH37 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ”
  &&  “ (hp_filter_offset (ne_len_pre - 1 ) (offset - 8 ) ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ ((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = (ne_len_pre - 1 )) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_9_2 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (offset < 8)) (PreH2 : (retval <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH4 : (INT_MIN <= retval)) (PreH5 : (retval <= INT_MAX)) (PreH6 : (m1 < 15)) (PreH7 : (tmp >= m1)) (PreH8 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH10 : (0 < base_low_level_spec)) (PreH11 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH12 : (0 <= hayoff_low_level_spec)) (PreH13 : (0 <= needleoff_low_level_spec)) (PreH14 : (3 <= ne_len_pre)) (PreH15 : (ne_len_pre <= 256)) (PreH16 : (ne_len_pre <= hs_len_pre)) (PreH17 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH18 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH19 : (length_low_level_spec <= INT_MAX)) (PreH20 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH21 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH22 : (ne = needle_pre)) (PreH23 : (m1 = (ne_len_pre - 1 ))) (PreH24 : (2 <= m1)) (PreH25 : (m1 <= 255)) (PreH26 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH28 : (1 <= shift1)) (PreH29 : (shift1 <= m1)) (PreH30 : (hp_filter_offset m1 offset )) (PreH31 : (0 <= position_2)) (PreH32 : (position_2 <= hs_len_pre)) (PreH33 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH35 : (0 <= tmp)) (PreH36 : (tmp <= m1)) (PreH37 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 (unsigned_last_nbits ((m1 - 8 )) (64)) ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = m1) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (offset < 8)) (PreH2 : (retval <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH4 : (INT_MIN <= retval)) (PreH5 : (retval <= INT_MAX)) (PreH6 : (m1 < 15)) (PreH7 : (tmp >= m1)) (PreH8 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH10 : (0 < base_low_level_spec)) (PreH11 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH12 : (0 <= hayoff_low_level_spec)) (PreH13 : (0 <= needleoff_low_level_spec)) (PreH14 : (3 <= ne_len_pre)) (PreH15 : (ne_len_pre <= 256)) (PreH16 : (ne_len_pre <= hs_len_pre)) (PreH17 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH18 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH19 : (length_low_level_spec <= INT_MAX)) (PreH20 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH21 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH22 : (ne = needle_pre)) (PreH23 : (m1 = (ne_len_pre - 1 ))) (PreH24 : (2 <= m1)) (PreH25 : (m1 <= 255)) (PreH26 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH28 : (1 <= shift1)) (PreH29 : (shift1 <= m1)) (PreH30 : (hp_filter_offset m1 offset )) (PreH31 : (0 <= position_2)) (PreH32 : (position_2 <= hs_len_pre)) (PreH33 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH35 : (0 <= tmp)) (PreH36 : (tmp <= m1)) (PreH37 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ”
  &&  “ (hp_filter_offset (ne_len_pre - 1 ) (unsigned_last_nbits (((ne_len_pre - 1 ) - 8 )) (64)) ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ ((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = (ne_len_pre - 1 )) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_9_3 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (offset >= 8)) (PreH2 : (retval_2 <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH4 : (INT_MIN <= retval_2)) (PreH5 : (retval_2 <= INT_MAX)) (PreH6 : (retval = 0)) (PreH7 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH8 : (INT_MIN <= retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (m1 >= 15)) (PreH11 : (tmp >= m1)) (PreH12 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH14 : (0 < base_low_level_spec)) (PreH15 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH16 : (0 <= hayoff_low_level_spec)) (PreH17 : (0 <= needleoff_low_level_spec)) (PreH18 : (3 <= ne_len_pre)) (PreH19 : (ne_len_pre <= 256)) (PreH20 : (ne_len_pre <= hs_len_pre)) (PreH21 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH22 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH23 : (length_low_level_spec <= INT_MAX)) (PreH24 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH25 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH26 : (ne = needle_pre)) (PreH27 : (m1 = (ne_len_pre - 1 ))) (PreH28 : (2 <= m1)) (PreH29 : (m1 <= 255)) (PreH30 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH31 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH32 : (1 <= shift1)) (PreH33 : (shift1 <= m1)) (PreH34 : (hp_filter_offset m1 offset )) (PreH35 : (0 <= position_2)) (PreH36 : (position_2 <= hs_len_pre)) (PreH37 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH39 : (0 <= tmp)) (PreH40 : (tmp <= m1)) (PreH41 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 (offset - 8 ) ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = m1) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (offset >= 8)) (PreH2 : (retval_2 <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH4 : (INT_MIN <= retval_2)) (PreH5 : (retval_2 <= INT_MAX)) (PreH6 : (retval = 0)) (PreH7 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH8 : (INT_MIN <= retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (m1 >= 15)) (PreH11 : (tmp >= m1)) (PreH12 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH14 : (0 < base_low_level_spec)) (PreH15 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH16 : (0 <= hayoff_low_level_spec)) (PreH17 : (0 <= needleoff_low_level_spec)) (PreH18 : (3 <= ne_len_pre)) (PreH19 : (ne_len_pre <= 256)) (PreH20 : (ne_len_pre <= hs_len_pre)) (PreH21 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH22 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH23 : (length_low_level_spec <= INT_MAX)) (PreH24 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH25 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH26 : (ne = needle_pre)) (PreH27 : (m1 = (ne_len_pre - 1 ))) (PreH28 : (2 <= m1)) (PreH29 : (m1 <= 255)) (PreH30 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH31 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH32 : (1 <= shift1)) (PreH33 : (shift1 <= m1)) (PreH34 : (hp_filter_offset m1 offset )) (PreH35 : (0 <= position_2)) (PreH36 : (position_2 <= hs_len_pre)) (PreH37 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH39 : (0 <= tmp)) (PreH40 : (tmp <= m1)) (PreH41 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ”
  &&  “ (hp_filter_offset (ne_len_pre - 1 ) (offset - 8 ) ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ ((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = (ne_len_pre - 1 )) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_9_4 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (offset < 8)) (PreH2 : (retval_2 <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH4 : (INT_MIN <= retval_2)) (PreH5 : (retval_2 <= INT_MAX)) (PreH6 : (retval = 0)) (PreH7 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH8 : (INT_MIN <= retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (m1 >= 15)) (PreH11 : (tmp >= m1)) (PreH12 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH14 : (0 < base_low_level_spec)) (PreH15 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH16 : (0 <= hayoff_low_level_spec)) (PreH17 : (0 <= needleoff_low_level_spec)) (PreH18 : (3 <= ne_len_pre)) (PreH19 : (ne_len_pre <= 256)) (PreH20 : (ne_len_pre <= hs_len_pre)) (PreH21 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH22 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH23 : (length_low_level_spec <= INT_MAX)) (PreH24 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH25 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH26 : (ne = needle_pre)) (PreH27 : (m1 = (ne_len_pre - 1 ))) (PreH28 : (2 <= m1)) (PreH29 : (m1 <= 255)) (PreH30 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH31 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH32 : (1 <= shift1)) (PreH33 : (shift1 <= m1)) (PreH34 : (hp_filter_offset m1 offset )) (PreH35 : (0 <= position_2)) (PreH36 : (position_2 <= hs_len_pre)) (PreH37 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH39 : (0 <= tmp)) (PreH40 : (tmp <= m1)) (PreH41 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 (m1 - 8 ) ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = m1) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (offset < 8)) (PreH2 : (retval_2 <> 0)) (PreH3 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH4 : (INT_MIN <= retval_2)) (PreH5 : (retval_2 <= INT_MAX)) (PreH6 : (retval = 0)) (PreH7 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH8 : (INT_MIN <= retval)) (PreH9 : (retval <= INT_MAX)) (PreH10 : (m1 >= 15)) (PreH11 : (tmp >= m1)) (PreH12 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH14 : (0 < base_low_level_spec)) (PreH15 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH16 : (0 <= hayoff_low_level_spec)) (PreH17 : (0 <= needleoff_low_level_spec)) (PreH18 : (3 <= ne_len_pre)) (PreH19 : (ne_len_pre <= 256)) (PreH20 : (ne_len_pre <= hs_len_pre)) (PreH21 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH22 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH23 : (length_low_level_spec <= INT_MAX)) (PreH24 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH25 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH26 : (ne = needle_pre)) (PreH27 : (m1 = (ne_len_pre - 1 ))) (PreH28 : (2 <= m1)) (PreH29 : (m1 <= 255)) (PreH30 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH31 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH32 : (1 <= shift1)) (PreH33 : (shift1 <= m1)) (PreH34 : (hp_filter_offset m1 offset )) (PreH35 : (0 <= position_2)) (PreH36 : (position_2 <= hs_len_pre)) (PreH37 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH39 : (0 <= tmp)) (PreH40 : (tmp <= m1)) (PreH41 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ”
  &&  “ (hp_filter_offset (ne_len_pre - 1 ) ((ne_len_pre - 1 ) - 8 ) ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ ((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = (ne_len_pre - 1 )) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_9_5 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH3 : (INT_MIN <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (m1 >= 15)) (PreH6 : (tmp >= m1)) (PreH7 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (0 < base_low_level_spec)) (PreH10 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH11 : (0 <= hayoff_low_level_spec)) (PreH12 : (0 <= needleoff_low_level_spec)) (PreH13 : (3 <= ne_len_pre)) (PreH14 : (ne_len_pre <= 256)) (PreH15 : (ne_len_pre <= hs_len_pre)) (PreH16 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH17 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH18 : (length_low_level_spec <= INT_MAX)) (PreH19 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH20 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH21 : (ne = needle_pre)) (PreH22 : (m1 = (ne_len_pre - 1 ))) (PreH23 : (2 <= m1)) (PreH24 : (m1 <= 255)) (PreH25 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH26 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH27 : (1 <= shift1)) (PreH28 : (shift1 <= m1)) (PreH29 : (hp_filter_offset m1 offset )) (PreH30 : (0 <= position_2)) (PreH31 : (position_2 <= hs_len_pre)) (PreH32 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH33 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH34 : (0 <= tmp)) (PreH35 : (tmp <= m1)) (PreH36 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = m1) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH3 : (INT_MIN <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (m1 >= 15)) (PreH6 : (tmp >= m1)) (PreH7 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (0 < base_low_level_spec)) (PreH10 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH11 : (0 <= hayoff_low_level_spec)) (PreH12 : (0 <= needleoff_low_level_spec)) (PreH13 : (3 <= ne_len_pre)) (PreH14 : (ne_len_pre <= 256)) (PreH15 : (ne_len_pre <= hs_len_pre)) (PreH16 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH17 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH18 : (length_low_level_spec <= INT_MAX)) (PreH19 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH20 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH21 : (ne = needle_pre)) (PreH22 : (m1 = (ne_len_pre - 1 ))) (PreH23 : (2 <= m1)) (PreH24 : (m1 <= 255)) (PreH25 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH26 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH27 : (1 <= shift1)) (PreH28 : (shift1 <= m1)) (PreH29 : (hp_filter_offset m1 offset )) (PreH30 : (0 <= position_2)) (PreH31 : (position_2 <= hs_len_pre)) (PreH32 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH33 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH34 : (0 <= tmp)) (PreH35 : (tmp <= m1)) (PreH36 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position + shift1 ))) X_low_level_spec ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ ((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position + shift1 ) ) ”
  &&  “ (tmp = (ne_len_pre - 1 )) ”
  &&  “ ((position + ne_len_pre ) <= hs_len_pre) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_10_1 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (shift1: Z) (ne: Z) (m1: Z) (search_end: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH2 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (0 < base_low_level_spec)) (PreH4 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH5 : (0 <= hayoff_low_level_spec)) (PreH6 : (0 <= needleoff_low_level_spec)) (PreH7 : (3 <= ne_len_pre)) (PreH8 : (ne_len_pre <= 256)) (PreH9 : (ne_len_pre <= hs_len_pre)) (PreH10 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH11 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH12 : (length_low_level_spec <= INT_MAX)) (PreH13 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH14 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 + shift1 ))) X_low_level_spec )) (PreH15 : (ne = needle_pre)) (PreH16 : (m1 = (ne_len_pre - 1 ))) (PreH17 : (2 <= m1)) (PreH18 : (m1 <= 255)) (PreH19 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH20 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH21 : (1 <= shift1)) (PreH22 : (shift1 <= m1)) (PreH23 : (hp_filter_offset m1 offset )) (PreH24 : (0 <= position_2)) (PreH25 : (position_2 <= hs_len_pre)) (PreH26 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 + shift1 ) )) (PreH29 : (tmp = m1)) (PreH30 : ((position_2 + ne_len_pre ) <= hs_len_pre)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ ((hs + (shift1 * sizeof(UCHAR))) = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (shift1: Z) (ne: Z) (m1: Z) (search_end: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH2 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (0 < base_low_level_spec)) (PreH4 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH5 : (0 <= hayoff_low_level_spec)) (PreH6 : (0 <= needleoff_low_level_spec)) (PreH7 : (3 <= ne_len_pre)) (PreH8 : (ne_len_pre <= 256)) (PreH9 : (ne_len_pre <= hs_len_pre)) (PreH10 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH11 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH12 : (length_low_level_spec <= INT_MAX)) (PreH13 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH14 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position_2 + shift1 ))) X_low_level_spec )) (PreH15 : (ne = needle_pre)) (PreH16 : (m1 = (ne_len_pre - 1 ))) (PreH17 : (2 <= m1)) (PreH18 : (m1 <= 255)) (PreH19 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH20 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH21 : (1 <= shift1)) (PreH22 : (shift1 <= m1)) (PreH23 : (hp_filter_offset m1 offset )) (PreH24 : (0 <= position_2)) (PreH25 : (position_2 <= hs_len_pre)) (PreH26 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position_2 + shift1 ) )) (PreH29 : (tmp = m1)) (PreH30 : ((position_2 + ne_len_pre ) <= hs_len_pre)),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) + (shift1 * sizeof(UCHAR))) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= m1) ”
  &&  “ (m1 <= (ne_len_pre - 1 )) ”
  &&  emp
).

Definition horspool_memmem_refinement_entail_wit_10_2 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp < m1)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (0 <= position_2)) (PreH26 : (position_2 <= hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)) (PreH31 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table_2 )
|--
  EX (table: (@list Z)) (position: Z),
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table_2: (@list Z)) (position_2: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp < m1)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position_2)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table_2 shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (0 <= position_2)) (PreH26 : (position_2 <= hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)))) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position_2 )) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)) (PreH31 : ((tmp = m1) -> (((position_2 + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position_2 ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  TT && emp 
|--
  EX (position: Z),
  “ (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ ((haystack_pre + ((position_2 * sizeof(UCHAR) ) * 1)) = ((base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ) + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  emp
).

Definition horspool_memmem_refinement_return_wit_1 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table: (@list Z)) (shift1: Z) (search_end: Z) (m1: Z) (ne: Z) (position: Z) (PreH1 : (hs > search_end)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (0 <= position)) (PreH26 : (position <= hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (0)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table: (@list Z)) (shift1: Z) (search_end: Z) (m1: Z) (ne: Z) (position: Z) (PreH1 : (hs > search_end)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (0 <= position)) (PreH26 : (position <= hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)),
  TT && emp 
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (0)))) X_low_level_spec ) ”
  &&  emp
).

Definition horspool_memmem_refinement_return_wit_1_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (tmp: Z) (hs: Z) (offset: Z) (table: (@list Z)) (shift1: Z) (search_end: Z) (m1: Z) (ne: Z) (position: Z) (PreH1 : (hs > search_end)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH22 : (1 <= shift1)) (PreH23 : (shift1 <= m1)) (PreH24 : (hp_filter_offset m1 offset )) (PreH25 : (0 <= position)) (PreH26 : (position <= hs_len_pre)) (PreH27 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH28 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH29 : (0 <= tmp)) (PreH30 : (tmp <= m1)),
  (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (0)))) X_low_level_spec )
.

Definition horspool_memmem_refinement_return_wit_2 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH3 : (INT_MIN <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (m1 < 15)) (PreH6 : (tmp >= m1)) (PreH7 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (0 < base_low_level_spec)) (PreH10 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH11 : (0 <= hayoff_low_level_spec)) (PreH12 : (0 <= needleoff_low_level_spec)) (PreH13 : (3 <= ne_len_pre)) (PreH14 : (ne_len_pre <= 256)) (PreH15 : (ne_len_pre <= hs_len_pre)) (PreH16 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH17 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH18 : (length_low_level_spec <= INT_MAX)) (PreH19 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH20 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH21 : (ne = needle_pre)) (PreH22 : (m1 = (ne_len_pre - 1 ))) (PreH23 : (2 <= m1)) (PreH24 : (m1 <= 255)) (PreH25 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH26 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH27 : (1 <= shift1)) (PreH28 : (shift1 <= m1)) (PreH29 : (hp_filter_offset m1 offset )) (PreH30 : (0 <= position)) (PreH31 : (position <= hs_len_pre)) (PreH32 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH33 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH34 : (0 <= tmp)) (PreH35 : (tmp <= m1)) (PreH36 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (hs)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH3 : (INT_MIN <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (m1 < 15)) (PreH6 : (tmp >= m1)) (PreH7 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (0 < base_low_level_spec)) (PreH10 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH11 : (0 <= hayoff_low_level_spec)) (PreH12 : (0 <= needleoff_low_level_spec)) (PreH13 : (3 <= ne_len_pre)) (PreH14 : (ne_len_pre <= 256)) (PreH15 : (ne_len_pre <= hs_len_pre)) (PreH16 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH17 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH18 : (length_low_level_spec <= INT_MAX)) (PreH19 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH20 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH21 : (ne = needle_pre)) (PreH22 : (m1 = (ne_len_pre - 1 ))) (PreH23 : (2 <= m1)) (PreH24 : (m1 <= 255)) (PreH25 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH26 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH27 : (1 <= shift1)) (PreH28 : (shift1 <= m1)) (PreH29 : (hp_filter_offset m1 offset )) (PreH30 : (0 <= position)) (PreH31 : (position <= hs_len_pre)) (PreH32 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH33 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH34 : (0 <= tmp)) (PreH35 : (tmp <= m1)) (PreH36 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  TT && emp 
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (hs)))) X_low_level_spec ) ”
  &&  emp
).

Definition horspool_memmem_refinement_return_wit_2_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval )) (PreH3 : (INT_MIN <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (m1 < 15)) (PreH6 : (tmp >= m1)) (PreH7 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (0 < base_low_level_spec)) (PreH10 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH11 : (0 <= hayoff_low_level_spec)) (PreH12 : (0 <= needleoff_low_level_spec)) (PreH13 : (3 <= ne_len_pre)) (PreH14 : (ne_len_pre <= 256)) (PreH15 : (ne_len_pre <= hs_len_pre)) (PreH16 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH17 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH18 : (length_low_level_spec <= INT_MAX)) (PreH19 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH20 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH21 : (ne = needle_pre)) (PreH22 : (m1 = (ne_len_pre - 1 ))) (PreH23 : (2 <= m1)) (PreH24 : (m1 <= 255)) (PreH25 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH26 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH27 : (1 <= shift1)) (PreH28 : (shift1 <= m1)) (PreH29 : (hp_filter_offset m1 offset )) (PreH30 : (0 <= position)) (PreH31 : (position <= hs_len_pre)) (PreH32 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH33 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH34 : (0 <= tmp)) (PreH35 : (tmp <= m1)) (PreH36 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (hs)))) X_low_level_spec )
.

Definition horspool_memmem_refinement_return_wit_3 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH3 : (INT_MIN <= retval_2)) (PreH4 : (retval_2 <= INT_MAX)) (PreH5 : (retval = 0)) (PreH6 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH7 : (INT_MIN <= retval)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (m1 >= 15)) (PreH10 : (tmp >= m1)) (PreH11 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH12 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (0 < base_low_level_spec)) (PreH14 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH15 : (0 <= hayoff_low_level_spec)) (PreH16 : (0 <= needleoff_low_level_spec)) (PreH17 : (3 <= ne_len_pre)) (PreH18 : (ne_len_pre <= 256)) (PreH19 : (ne_len_pre <= hs_len_pre)) (PreH20 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH21 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH22 : (length_low_level_spec <= INT_MAX)) (PreH23 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH24 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH25 : (ne = needle_pre)) (PreH26 : (m1 = (ne_len_pre - 1 ))) (PreH27 : (2 <= m1)) (PreH28 : (m1 <= 255)) (PreH29 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH30 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH31 : (1 <= shift1)) (PreH32 : (shift1 <= m1)) (PreH33 : (hp_filter_offset m1 offset )) (PreH34 : (0 <= position)) (PreH35 : (position <= hs_len_pre)) (PreH36 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH37 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH38 : (0 <= tmp)) (PreH39 : (tmp <= m1)) (PreH40 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (hs)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH3 : (INT_MIN <= retval_2)) (PreH4 : (retval_2 <= INT_MAX)) (PreH5 : (retval = 0)) (PreH6 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH7 : (INT_MIN <= retval)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (m1 >= 15)) (PreH10 : (tmp >= m1)) (PreH11 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH12 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (0 < base_low_level_spec)) (PreH14 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH15 : (0 <= hayoff_low_level_spec)) (PreH16 : (0 <= needleoff_low_level_spec)) (PreH17 : (3 <= ne_len_pre)) (PreH18 : (ne_len_pre <= 256)) (PreH19 : (ne_len_pre <= hs_len_pre)) (PreH20 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH21 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH22 : (length_low_level_spec <= INT_MAX)) (PreH23 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH24 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH25 : (ne = needle_pre)) (PreH26 : (m1 = (ne_len_pre - 1 ))) (PreH27 : (2 <= m1)) (PreH28 : (m1 <= 255)) (PreH29 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH30 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH31 : (1 <= shift1)) (PreH32 : (shift1 <= m1)) (PreH33 : (hp_filter_offset m1 offset )) (PreH34 : (0 <= position)) (PreH35 : (position <= hs_len_pre)) (PreH36 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH37 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH38 : (0 <= tmp)) (PreH39 : (tmp <= m1)) (PreH40 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  TT && emp 
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (hs)))) X_low_level_spec ) ”
  &&  emp
).

Definition horspool_memmem_refinement_return_wit_3_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + ((-base_low_level_spec) * sizeof(UCHAR))) needleoff_low_level_spec m1 retval_2 )) (PreH3 : (INT_MIN <= retval_2)) (PreH4 : (retval_2 <= INT_MAX)) (PreH5 : (retval = 0)) (PreH6 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH7 : (INT_MIN <= retval)) (PreH8 : (retval <= INT_MAX)) (PreH9 : (m1 >= 15)) (PreH10 : (tmp >= m1)) (PreH11 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH12 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH13 : (0 < base_low_level_spec)) (PreH14 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH15 : (0 <= hayoff_low_level_spec)) (PreH16 : (0 <= needleoff_low_level_spec)) (PreH17 : (3 <= ne_len_pre)) (PreH18 : (ne_len_pre <= 256)) (PreH19 : (ne_len_pre <= hs_len_pre)) (PreH20 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH21 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH22 : (length_low_level_spec <= INT_MAX)) (PreH23 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH24 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH25 : (ne = needle_pre)) (PreH26 : (m1 = (ne_len_pre - 1 ))) (PreH27 : (2 <= m1)) (PreH28 : (m1 <= 255)) (PreH29 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH30 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH31 : (1 <= shift1)) (PreH32 : (shift1 <= m1)) (PreH33 : (hp_filter_offset m1 offset )) (PreH34 : (0 <= position)) (PreH35 : (position <= hs_len_pre)) (PreH36 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH37 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH38 : (0 <= tmp)) (PreH39 : (tmp <= m1)) (PreH40 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (hs)))) X_low_level_spec )
.

Definition horspool_memmem_refinement_return_wit_4 :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre < ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (0)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre < ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  TT && emp 
|--
  “ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (0)))) X_low_level_spec ) ”
  &&  emp
).

Definition horspool_memmem_refinement_return_wit_4_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre < ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (0)))) X_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_1_pure :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre >= ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  ((( &( "offset" ) )) # UInt64  |-> 0)
  **  ((( &( "m1" ) )) # UInt64  |-> (ne_len_pre - 1 ))
  **  ((( &( "shift1" ) )) # UInt64  |-> 0)
  **  ((( &( "tmp" ) )) # UInt64  |-> 0)
  **  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  ((( &( "search_end" ) )) # Ptr  |-> (haystack_pre + ((hs_len_pre + (-ne_len_pre) ) * sizeof(UCHAR))))
  **  ((( &( "ne" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "hs" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
  **  ((( &( "hs_len" ) )) # UInt64  |-> hs_len_pre)
  **  ((( &( "needle" ) )) # Ptr  |-> needle_pre)
  **  ((( &( "ne_len" ) )) # UInt64  |-> ne_len_pre)
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ ((( &( "shift" ) ) + (0 * sizeof(UCHAR))) = ( &( "shift" ) )) ”
  &&  “ (0 = 0) ”
  &&  “ (256 = 256) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_1_aux :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (PreH1 : (hs_len_pre >= ne_len_pre)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (0 <= hs_len_pre)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )),
  (UCharArray.undef_full ( &( "shift" ) ) 256 )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ ((( &( "shift" ) ) + (0 * sizeof(UCHAR))) = ( &( "shift" ) )) ”
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
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (i < m1)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hs = haystack_pre)) (PreH22 : (offset = 0)) (PreH23 : (1 <= i)) (PreH24 : (i <= m1)) (PreH25 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH26 : (tmp = 0)) (PreH27 : (shift1 = 0)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((ne + (i * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ”
  &&  “ (1 <= (needleoff_low_level_spec + i )) ”
  &&  “ ((needleoff_low_level_spec + i ) < length_low_level_spec) ”
  &&  “ ((needle_pre + (i * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ”
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (shift1 <= UINT64_MAX)) (PreH2 : (tmp <= UINT64_MAX)) (PreH3 : (offset <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (shift1 >= 0)) (PreH8 : (tmp >= 0)) (PreH9 : (offset >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (i <= INT_MAX)) (PreH14 : (i >= INT_MIN)) (PreH15 : (i < m1)) (PreH16 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH18 : (0 < base_low_level_spec)) (PreH19 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH20 : (0 <= hayoff_low_level_spec)) (PreH21 : (0 <= needleoff_low_level_spec)) (PreH22 : (3 <= ne_len_pre)) (PreH23 : (ne_len_pre <= 256)) (PreH24 : (ne_len_pre <= hs_len_pre)) (PreH25 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH26 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH27 : (length_low_level_spec <= INT_MAX)) (PreH28 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH29 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH30 : (ne = needle_pre)) (PreH31 : (m1 = (ne_len_pre - 1 ))) (PreH32 : (2 <= m1)) (PreH33 : (m1 <= 255)) (PreH34 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH35 : (hs = haystack_pre)) (PreH36 : (offset = 0)) (PreH37 : (1 <= i)) (PreH38 : (i <= m1)) (PreH39 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH40 : (tmp = 0)) (PreH41 : (shift1 = 0)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((needle_pre + (i * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ”
  &&  “ ((needle_pre + (i * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ”
).

Definition horspool_memmem_refinement_partial_solve_wit_2_pure_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (shift1 <= UINT64_MAX)) (PreH2 : (tmp <= UINT64_MAX)) (PreH3 : (offset <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (shift1 >= 0)) (PreH8 : (tmp >= 0)) (PreH9 : (offset >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (i <= INT_MAX)) (PreH14 : (i >= INT_MIN)) (PreH15 : (i < m1)) (PreH16 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH18 : (0 < base_low_level_spec)) (PreH19 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH20 : (0 <= hayoff_low_level_spec)) (PreH21 : (0 <= needleoff_low_level_spec)) (PreH22 : (3 <= ne_len_pre)) (PreH23 : (ne_len_pre <= 256)) (PreH24 : (ne_len_pre <= hs_len_pre)) (PreH25 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH26 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH27 : (length_low_level_spec <= INT_MAX)) (PreH28 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH29 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH30 : (ne = needle_pre)) (PreH31 : (m1 = (ne_len_pre - 1 ))) (PreH32 : (2 <= m1)) (PreH33 : (m1 <= 255)) (PreH34 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH35 : (hs = haystack_pre)) (PreH36 : (offset = 0)) (PreH37 : (1 <= i)) (PreH38 : (i <= m1)) (PreH39 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH40 : (tmp = 0)) (PreH41 : (shift1 = 0)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((needle_pre + (i * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_2_pure_split_goal_2 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (shift1 <= UINT64_MAX)) (PreH2 : (tmp <= UINT64_MAX)) (PreH3 : (offset <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (shift1 >= 0)) (PreH8 : (tmp >= 0)) (PreH9 : (offset >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (i <= INT_MAX)) (PreH14 : (i >= INT_MIN)) (PreH15 : (i < m1)) (PreH16 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH18 : (0 < base_low_level_spec)) (PreH19 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH20 : (0 <= hayoff_low_level_spec)) (PreH21 : (0 <= needleoff_low_level_spec)) (PreH22 : (3 <= ne_len_pre)) (PreH23 : (ne_len_pre <= 256)) (PreH24 : (ne_len_pre <= hs_len_pre)) (PreH25 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH26 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH27 : (length_low_level_spec <= INT_MAX)) (PreH28 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH29 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH30 : (ne = needle_pre)) (PreH31 : (m1 = (ne_len_pre - 1 ))) (PreH32 : (2 <= m1)) (PreH33 : (m1 <= 255)) (PreH34 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH35 : (hs = haystack_pre)) (PreH36 : (offset = 0)) (PreH37 : (1 <= i)) (PreH38 : (i <= m1)) (PreH39 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH40 : (tmp = 0)) (PreH41 : (shift1 = 0)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((needle_pre + (i * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_2_aux :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (i < m1)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hs = haystack_pre)) (PreH22 : (offset = 0)) (PreH23 : (1 <= i)) (PreH24 : (i <= m1)) (PreH25 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH26 : (tmp = 0)) (PreH27 : (shift1 = 0)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ ((ne + (i * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ”
  &&  “ (1 <= (needleoff_low_level_spec + i )) ”
  &&  “ ((needleoff_low_level_spec + i ) < length_low_level_spec) ”
  &&  “ ((needle_pre + (i * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + i ) * sizeof(UCHAR) ) )) ”
  &&  “ (i < m1) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (i < m1)) (PreH5 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (0 < base_low_level_spec)) (PreH8 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH9 : (0 <= hayoff_low_level_spec)) (PreH10 : (0 <= needleoff_low_level_spec)) (PreH11 : (3 <= ne_len_pre)) (PreH12 : (ne_len_pre <= 256)) (PreH13 : (ne_len_pre <= hs_len_pre)) (PreH14 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH15 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH16 : (length_low_level_spec <= INT_MAX)) (PreH17 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH18 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH19 : (ne = needle_pre)) (PreH20 : (m1 = (ne_len_pre - 1 ))) (PreH21 : (2 <= m1)) (PreH22 : (m1 <= 255)) (PreH23 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH24 : (hs = haystack_pre)) (PreH25 : (offset = 0)) (PreH26 : (1 <= i)) (PreH27 : (i <= m1)) (PreH28 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH29 : (tmp = 0)) (PreH30 : (shift1 = 0)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + i )))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (i < m1) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hs = haystack_pre) ”
  &&  “ (offset = 0) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= m1) ”
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ”
  &&  “ (tmp = 0) ”
  &&  “ (shift1 = 0) ”
  &&  (((( &( "shift" ) ) + (retval * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "shift" ) ) retval 0 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_4_pure :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (i >= m1)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hs = haystack_pre)) (PreH22 : (offset = 0)) (PreH23 : (1 <= i)) (PreH24 : (i <= m1)) (PreH25 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH26 : (tmp = 0)) (PreH27 : (shift1 = 0)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((ne + (m1 * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + m1 ) * sizeof(UCHAR) ) )) ”
  &&  “ (1 <= (needleoff_low_level_spec + m1 )) ”
  &&  “ ((needleoff_low_level_spec + m1 ) < length_low_level_spec) ”
  &&  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (shift1 <= UINT64_MAX)) (PreH2 : (tmp <= UINT64_MAX)) (PreH3 : (offset <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (shift1 >= 0)) (PreH8 : (tmp >= 0)) (PreH9 : (offset >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (i >= m1)) (PreH14 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH15 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (0 < base_low_level_spec)) (PreH17 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH18 : (0 <= hayoff_low_level_spec)) (PreH19 : (0 <= needleoff_low_level_spec)) (PreH20 : (3 <= ne_len_pre)) (PreH21 : (ne_len_pre <= 256)) (PreH22 : (ne_len_pre <= hs_len_pre)) (PreH23 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH24 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH25 : (length_low_level_spec <= INT_MAX)) (PreH26 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH27 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH28 : (ne = needle_pre)) (PreH29 : (m1 = (ne_len_pre - 1 ))) (PreH30 : (2 <= m1)) (PreH31 : (m1 <= 255)) (PreH32 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH33 : (hs = haystack_pre)) (PreH34 : (offset = 0)) (PreH35 : (1 <= i)) (PreH36 : (i <= m1)) (PreH37 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH38 : (tmp = 0)) (PreH39 : (shift1 = 0)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
  &&  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
).

Definition horspool_memmem_refinement_partial_solve_wit_4_pure_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (shift1 <= UINT64_MAX)) (PreH2 : (tmp <= UINT64_MAX)) (PreH3 : (offset <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (shift1 >= 0)) (PreH8 : (tmp >= 0)) (PreH9 : (offset >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (i >= m1)) (PreH14 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH15 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (0 < base_low_level_spec)) (PreH17 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH18 : (0 <= hayoff_low_level_spec)) (PreH19 : (0 <= needleoff_low_level_spec)) (PreH20 : (3 <= ne_len_pre)) (PreH21 : (ne_len_pre <= 256)) (PreH22 : (ne_len_pre <= hs_len_pre)) (PreH23 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH24 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH25 : (length_low_level_spec <= INT_MAX)) (PreH26 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH27 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH28 : (ne = needle_pre)) (PreH29 : (m1 = (ne_len_pre - 1 ))) (PreH30 : (2 <= m1)) (PreH31 : (m1 <= 255)) (PreH32 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH33 : (hs = haystack_pre)) (PreH34 : (offset = 0)) (PreH35 : (1 <= i)) (PreH36 : (i <= m1)) (PreH37 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH38 : (tmp = 0)) (PreH39 : (shift1 = 0)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_4_pure_split_goal_2 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (shift1 <= UINT64_MAX)) (PreH2 : (tmp <= UINT64_MAX)) (PreH3 : (offset <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (shift1 >= 0)) (PreH8 : (tmp >= 0)) (PreH9 : (offset >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (i >= m1)) (PreH14 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH15 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (0 < base_low_level_spec)) (PreH17 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH18 : (0 <= hayoff_low_level_spec)) (PreH19 : (0 <= needleoff_low_level_spec)) (PreH20 : (3 <= ne_len_pre)) (PreH21 : (ne_len_pre <= 256)) (PreH22 : (ne_len_pre <= hs_len_pre)) (PreH23 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH24 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH25 : (length_low_level_spec <= INT_MAX)) (PreH26 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH27 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH28 : (ne = needle_pre)) (PreH29 : (m1 = (ne_len_pre - 1 ))) (PreH30 : (2 <= m1)) (PreH31 : (m1 <= 255)) (PreH32 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH33 : (hs = haystack_pre)) (PreH34 : (offset = 0)) (PreH35 : (1 <= i)) (PreH36 : (i <= m1)) (PreH37 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH38 : (tmp = 0)) (PreH39 : (shift1 = 0)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_4_aux :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (PreH1 : (i >= m1)) (PreH2 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (0 < base_low_level_spec)) (PreH5 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH6 : (0 <= hayoff_low_level_spec)) (PreH7 : (0 <= needleoff_low_level_spec)) (PreH8 : (3 <= ne_len_pre)) (PreH9 : (ne_len_pre <= 256)) (PreH10 : (ne_len_pre <= hs_len_pre)) (PreH11 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH12 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH13 : (length_low_level_spec <= INT_MAX)) (PreH14 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH15 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH16 : (ne = needle_pre)) (PreH17 : (m1 = (ne_len_pre - 1 ))) (PreH18 : (2 <= m1)) (PreH19 : (m1 <= 255)) (PreH20 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH21 : (hs = haystack_pre)) (PreH22 : (offset = 0)) (PreH23 : (1 <= i)) (PreH24 : (i <= m1)) (PreH25 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH26 : (tmp = 0)) (PreH27 : (shift1 = 0)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ ((ne + (m1 * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + m1 ) * sizeof(UCHAR) ) )) ”
  &&  “ (1 <= (needleoff_low_level_spec + m1 )) ”
  &&  “ ((needleoff_low_level_spec + m1 ) < length_low_level_spec) ”
  &&  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
  &&  “ (i >= m1) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (i >= m1)) (PreH5 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (0 < base_low_level_spec)) (PreH8 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH9 : (0 <= hayoff_low_level_spec)) (PreH10 : (0 <= needleoff_low_level_spec)) (PreH11 : (3 <= ne_len_pre)) (PreH12 : (ne_len_pre <= 256)) (PreH13 : (ne_len_pre <= hs_len_pre)) (PreH14 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH15 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH16 : (length_low_level_spec <= INT_MAX)) (PreH17 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH18 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH19 : (ne = needle_pre)) (PreH20 : (m1 = (ne_len_pre - 1 ))) (PreH21 : (2 <= m1)) (PreH22 : (m1 <= 255)) (PreH23 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH24 : (hs = haystack_pre)) (PreH25 : (offset = 0)) (PreH26 : (1 <= i)) (PreH27 : (i <= m1)) (PreH28 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH29 : (tmp = 0)) (PreH30 : (shift1 = 0)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (i >= m1) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hs = haystack_pre) ”
  &&  “ (offset = 0) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= m1) ”
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ”
  &&  “ (tmp = 0) ”
  &&  “ (shift1 = 0) ”
  &&  (((( &( "shift" ) ) + (retval * sizeof(UCHAR)))) # UChar  |-> (Znth retval table 0))
  **  (UCharArray.missing_i ( &( "shift" ) ) retval 0 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_6_pure :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (i >= m1)) (PreH5 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (0 < base_low_level_spec)) (PreH8 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH9 : (0 <= hayoff_low_level_spec)) (PreH10 : (0 <= needleoff_low_level_spec)) (PreH11 : (3 <= ne_len_pre)) (PreH12 : (ne_len_pre <= 256)) (PreH13 : (ne_len_pre <= hs_len_pre)) (PreH14 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH15 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH16 : (length_low_level_spec <= INT_MAX)) (PreH17 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH18 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH19 : (ne = needle_pre)) (PreH20 : (m1 = (ne_len_pre - 1 ))) (PreH21 : (2 <= m1)) (PreH22 : (m1 <= 255)) (PreH23 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH24 : (hs = haystack_pre)) (PreH25 : (offset = 0)) (PreH26 : (1 <= i)) (PreH27 : (i <= m1)) (PreH28 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH29 : (tmp = 0)) (PreH30 : (shift1 = 0)),
  (UCharArray.full ( &( "shift" ) ) 256 table )
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
  “ ((ne + (m1 * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + m1 ) * sizeof(UCHAR) ) )) ”
  &&  “ (1 <= (needleoff_low_level_spec + m1 )) ”
  &&  “ ((needleoff_low_level_spec + m1 ) < length_low_level_spec) ”
  &&  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) <= UINT64_MAX)) (PreH2 : (tmp <= UINT64_MAX)) (PreH3 : (offset <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : ((unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) >= 0)) (PreH8 : (tmp >= 0)) (PreH9 : (offset >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (i >= m1)) (PreH17 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH18 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH19 : (0 < base_low_level_spec)) (PreH20 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH21 : (0 <= hayoff_low_level_spec)) (PreH22 : (0 <= needleoff_low_level_spec)) (PreH23 : (3 <= ne_len_pre)) (PreH24 : (ne_len_pre <= 256)) (PreH25 : (ne_len_pre <= hs_len_pre)) (PreH26 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH27 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH28 : (length_low_level_spec <= INT_MAX)) (PreH29 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH30 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH31 : (ne = needle_pre)) (PreH32 : (m1 = (ne_len_pre - 1 ))) (PreH33 : (2 <= m1)) (PreH34 : (m1 <= 255)) (PreH35 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH36 : (hs = haystack_pre)) (PreH37 : (offset = 0)) (PreH38 : (1 <= i)) (PreH39 : (i <= m1)) (PreH40 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH41 : (tmp = 0)) (PreH42 : (shift1 = 0)),
  (UCharArray.full ( &( "shift" ) ) 256 table )
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
  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
  &&  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
).

Definition horspool_memmem_refinement_partial_solve_wit_6_pure_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) <= UINT64_MAX)) (PreH2 : (tmp <= UINT64_MAX)) (PreH3 : (offset <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : ((unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) >= 0)) (PreH8 : (tmp >= 0)) (PreH9 : (offset >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (i >= m1)) (PreH17 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH18 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH19 : (0 < base_low_level_spec)) (PreH20 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH21 : (0 <= hayoff_low_level_spec)) (PreH22 : (0 <= needleoff_low_level_spec)) (PreH23 : (3 <= ne_len_pre)) (PreH24 : (ne_len_pre <= 256)) (PreH25 : (ne_len_pre <= hs_len_pre)) (PreH26 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH27 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH28 : (length_low_level_spec <= INT_MAX)) (PreH29 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH30 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH31 : (ne = needle_pre)) (PreH32 : (m1 = (ne_len_pre - 1 ))) (PreH33 : (2 <= m1)) (PreH34 : (m1 <= 255)) (PreH35 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH36 : (hs = haystack_pre)) (PreH37 : (offset = 0)) (PreH38 : (1 <= i)) (PreH39 : (i <= m1)) (PreH40 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH41 : (tmp = 0)) (PreH42 : (shift1 = 0)),
  (UCharArray.full ( &( "shift" ) ) 256 table )
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
  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_6_pure_split_goal_2 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) <= UINT64_MAX)) (PreH2 : (tmp <= UINT64_MAX)) (PreH3 : (offset <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : ((unsigned_last_nbits ((m1 - (unsigned_last_nbits ((Znth retval table 0)) (64)) )) (64)) >= 0)) (PreH8 : (tmp >= 0)) (PreH9 : (offset >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH14 : (0 <= retval)) (PreH15 : (retval < 256)) (PreH16 : (i >= m1)) (PreH17 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH18 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH19 : (0 < base_low_level_spec)) (PreH20 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH21 : (0 <= hayoff_low_level_spec)) (PreH22 : (0 <= needleoff_low_level_spec)) (PreH23 : (3 <= ne_len_pre)) (PreH24 : (ne_len_pre <= 256)) (PreH25 : (ne_len_pre <= hs_len_pre)) (PreH26 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH27 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH28 : (length_low_level_spec <= INT_MAX)) (PreH29 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH30 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH31 : (ne = needle_pre)) (PreH32 : (m1 = (ne_len_pre - 1 ))) (PreH33 : (2 <= m1)) (PreH34 : (m1 <= 255)) (PreH35 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH36 : (hs = haystack_pre)) (PreH37 : (offset = 0)) (PreH38 : (1 <= i)) (PreH39 : (i <= m1)) (PreH40 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH41 : (tmp = 0)) (PreH42 : (shift1 = 0)),
  (UCharArray.full ( &( "shift" ) ) 256 table )
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
  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_6_aux :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (i >= m1)) (PreH5 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH7 : (0 < base_low_level_spec)) (PreH8 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH9 : (0 <= hayoff_low_level_spec)) (PreH10 : (0 <= needleoff_low_level_spec)) (PreH11 : (3 <= ne_len_pre)) (PreH12 : (ne_len_pre <= 256)) (PreH13 : (ne_len_pre <= hs_len_pre)) (PreH14 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH15 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH16 : (length_low_level_spec <= INT_MAX)) (PreH17 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH18 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH19 : (ne = needle_pre)) (PreH20 : (m1 = (ne_len_pre - 1 ))) (PreH21 : (2 <= m1)) (PreH22 : (m1 <= 255)) (PreH23 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH24 : (hs = haystack_pre)) (PreH25 : (offset = 0)) (PreH26 : (1 <= i)) (PreH27 : (i <= m1)) (PreH28 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH29 : (tmp = 0)) (PreH30 : (shift1 = 0)),
  (UCharArray.full ( &( "shift" ) ) 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
|--
  “ ((ne + (m1 * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + m1 ) * sizeof(UCHAR) ) )) ”
  &&  “ (1 <= (needleoff_low_level_spec + m1 )) ”
  &&  “ ((needleoff_low_level_spec + m1 ) < length_low_level_spec) ”
  &&  “ ((needle_pre + ((ne_len_pre - 1 ) * sizeof(UCHAR))) = (base_low_level_spec + ((needleoff_low_level_spec + (ne_len_pre - 1 ) ) * sizeof(UCHAR) ) )) ”
  &&  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (i >= m1) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
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
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (shift1: Z) (tmp: Z) (table: (@list Z)) (i: Z) (offset: Z) (hs: Z) (search_end: Z) (m1: Z) (ne: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < 256)) (PreH4 : (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))) (PreH5 : (0 <= retval)) (PreH6 : (retval < 256)) (PreH7 : (i >= m1)) (PreH8 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH10 : (0 < base_low_level_spec)) (PreH11 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH12 : (0 <= hayoff_low_level_spec)) (PreH13 : (0 <= needleoff_low_level_spec)) (PreH14 : (3 <= ne_len_pre)) (PreH15 : (ne_len_pre <= 256)) (PreH16 : (ne_len_pre <= hs_len_pre)) (PreH17 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH18 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH19 : (length_low_level_spec <= INT_MAX)) (PreH20 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH21 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (0)) X_low_level_spec )) (PreH22 : (ne = needle_pre)) (PreH23 : (m1 = (ne_len_pre - 1 ))) (PreH24 : (2 <= m1)) (PreH25 : (m1 <= 255)) (PreH26 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH27 : (hs = haystack_pre)) (PreH28 : (offset = 0)) (PreH29 : (1 <= i)) (PreH30 : (i <= m1)) (PreH31 : (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table )) (PreH32 : (tmp = 0)) (PreH33 : (shift1 = 0)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (retval_2 = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ”
  &&  “ (0 <= retval_2) ”
  &&  “ (retval_2 < 256) ”
  &&  “ (retval = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))) ”
  &&  “ (0 <= retval) ”
  &&  “ (retval < 256) ”
  &&  “ (i >= m1) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hs = haystack_pre) ”
  &&  “ (offset = 0) ”
  &&  “ (1 <= i) ”
  &&  “ (i <= m1) ”
  &&  “ (hp_table_prefix bytes_low_level_spec needleoff_low_level_spec i table ) ”
  &&  “ (tmp = 0) ”
  &&  “ (shift1 = 0) ”
  &&  (((( &( "shift" ) ) + (retval_2 * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "shift" ) ) retval_2 0 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_8_pure :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH2 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (0 < base_low_level_spec)) (PreH4 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH5 : (0 <= hayoff_low_level_spec)) (PreH6 : (0 <= needleoff_low_level_spec)) (PreH7 : (3 <= ne_len_pre)) (PreH8 : (ne_len_pre <= 256)) (PreH9 : (ne_len_pre <= hs_len_pre)) (PreH10 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH11 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH12 : (length_low_level_spec <= INT_MAX)) (PreH13 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH14 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec )) (PreH15 : (ne = needle_pre)) (PreH16 : (m1 = (ne_len_pre - 1 ))) (PreH17 : (2 <= m1)) (PreH18 : (m1 <= 255)) (PreH19 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH20 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH21 : (1 <= shift1)) (PreH22 : (shift1 <= m1)) (PreH23 : (hp_filter_offset m1 offset )) (PreH24 : (m1 <= position)) (PreH25 : (position < hs_len_pre)) (PreH26 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) )) (PreH28 : (0 <= tmp)) (PreH29 : (tmp <= m1)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (hs = (base_low_level_spec + ((hs + ((-base_low_level_spec) * sizeof(UCHAR))) * sizeof(UCHAR) ) )) ”
  &&  “ ((hs + ((-base_low_level_spec) * sizeof(UCHAR))) < length_low_level_spec) ”
  &&  “ (1 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH14 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH15 : (0 < base_low_level_spec)) (PreH16 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH17 : (0 <= hayoff_low_level_spec)) (PreH18 : (0 <= needleoff_low_level_spec)) (PreH19 : (3 <= ne_len_pre)) (PreH20 : (ne_len_pre <= 256)) (PreH21 : (ne_len_pre <= hs_len_pre)) (PreH22 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH23 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH24 : (length_low_level_spec <= INT_MAX)) (PreH25 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH26 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec )) (PreH27 : (ne = needle_pre)) (PreH28 : (m1 = (ne_len_pre - 1 ))) (PreH29 : (2 <= m1)) (PreH30 : (m1 <= 255)) (PreH31 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH32 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH33 : (1 <= shift1)) (PreH34 : (shift1 <= m1)) (PreH35 : (hp_filter_offset m1 offset )) (PreH36 : (m1 <= position)) (PreH37 : (position < hs_len_pre)) (PreH38 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH39 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) )) (PreH40 : (0 <= tmp)) (PreH41 : (tmp <= m1)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (1 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
  &&  “ ((hs + ((-base_low_level_spec) * sizeof(UCHAR))) < length_low_level_spec) ”
).

Definition horspool_memmem_refinement_partial_solve_wit_8_pure_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH14 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH15 : (0 < base_low_level_spec)) (PreH16 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH17 : (0 <= hayoff_low_level_spec)) (PreH18 : (0 <= needleoff_low_level_spec)) (PreH19 : (3 <= ne_len_pre)) (PreH20 : (ne_len_pre <= 256)) (PreH21 : (ne_len_pre <= hs_len_pre)) (PreH22 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH23 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH24 : (length_low_level_spec <= INT_MAX)) (PreH25 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH26 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec )) (PreH27 : (ne = needle_pre)) (PreH28 : (m1 = (ne_len_pre - 1 ))) (PreH29 : (2 <= m1)) (PreH30 : (m1 <= 255)) (PreH31 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH32 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH33 : (1 <= shift1)) (PreH34 : (shift1 <= m1)) (PreH35 : (hp_filter_offset m1 offset )) (PreH36 : (m1 <= position)) (PreH37 : (position < hs_len_pre)) (PreH38 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH39 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) )) (PreH40 : (0 <= tmp)) (PreH41 : (tmp <= m1)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (1 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_8_pure_split_goal_2 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH14 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH15 : (0 < base_low_level_spec)) (PreH16 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH17 : (0 <= hayoff_low_level_spec)) (PreH18 : (0 <= needleoff_low_level_spec)) (PreH19 : (3 <= ne_len_pre)) (PreH20 : (ne_len_pre <= 256)) (PreH21 : (ne_len_pre <= hs_len_pre)) (PreH22 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH23 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH24 : (length_low_level_spec <= INT_MAX)) (PreH25 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH26 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec )) (PreH27 : (ne = needle_pre)) (PreH28 : (m1 = (ne_len_pre - 1 ))) (PreH29 : (2 <= m1)) (PreH30 : (m1 <= 255)) (PreH31 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH32 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH33 : (1 <= shift1)) (PreH34 : (shift1 <= m1)) (PreH35 : (hp_filter_offset m1 offset )) (PreH36 : (m1 <= position)) (PreH37 : (position < hs_len_pre)) (PreH38 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH39 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) )) (PreH40 : (0 <= tmp)) (PreH41 : (tmp <= m1)),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((hs + ((-base_low_level_spec) * sizeof(UCHAR))) < length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_8_aux :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH2 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH3 : (0 < base_low_level_spec)) (PreH4 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH5 : (0 <= hayoff_low_level_spec)) (PreH6 : (0 <= needleoff_low_level_spec)) (PreH7 : (3 <= ne_len_pre)) (PreH8 : (ne_len_pre <= 256)) (PreH9 : (ne_len_pre <= hs_len_pre)) (PreH10 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH11 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH12 : (length_low_level_spec <= INT_MAX)) (PreH13 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH14 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec )) (PreH15 : (ne = needle_pre)) (PreH16 : (m1 = (ne_len_pre - 1 ))) (PreH17 : (2 <= m1)) (PreH18 : (m1 <= 255)) (PreH19 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH20 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH21 : (1 <= shift1)) (PreH22 : (shift1 <= m1)) (PreH23 : (hp_filter_offset m1 offset )) (PreH24 : (m1 <= position)) (PreH25 : (position < hs_len_pre)) (PreH26 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH27 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) )) (PreH28 : (0 <= tmp)) (PreH29 : (tmp <= m1)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (hs = (base_low_level_spec + ((hs + ((-base_low_level_spec) * sizeof(UCHAR))) * sizeof(UCHAR) ) )) ”
  &&  “ ((hs + ((-base_low_level_spec) * sizeof(UCHAR))) < length_low_level_spec) ”
  &&  “ (1 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (m1 <= position) ”
  &&  “ (position < hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_8 := horspool_memmem_refinement_partial_solve_wit_8_pure -> horspool_memmem_refinement_partial_solve_wit_8_aux.

Definition horspool_memmem_refinement_partial_solve_wit_9 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (m1: Z) (ne: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval = (hp_hash_at (bytes_low_level_spec) ((hs + ((-base_low_level_spec) * sizeof(UCHAR))))))) (PreH2 : (0 <= retval)) (PreH3 : (retval < 256)) (PreH4 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH6 : (0 < base_low_level_spec)) (PreH7 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH8 : (0 <= hayoff_low_level_spec)) (PreH9 : (0 <= needleoff_low_level_spec)) (PreH10 : (3 <= ne_len_pre)) (PreH11 : (ne_len_pre <= 256)) (PreH12 : (ne_len_pre <= hs_len_pre)) (PreH13 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH14 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH15 : (length_low_level_spec <= INT_MAX)) (PreH16 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH17 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) ((position - m1 ))) X_low_level_spec )) (PreH18 : (ne = needle_pre)) (PreH19 : (m1 = (ne_len_pre - 1 ))) (PreH20 : (2 <= m1)) (PreH21 : (m1 <= 255)) (PreH22 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH23 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH24 : (1 <= shift1)) (PreH25 : (shift1 <= m1)) (PreH26 : (hp_filter_offset m1 offset )) (PreH27 : (m1 <= position)) (PreH28 : (position < hs_len_pre)) (PreH29 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH30 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) )) (PreH31 : (0 <= tmp)) (PreH32 : (tmp <= m1)),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (retval = (hp_hash_at (bytes_low_level_spec) ((hs + ((-base_low_level_spec) * sizeof(UCHAR)))))) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (m1 <= position) ”
  &&  “ (position < hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre (position - m1 ) ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  (((( &( "shift" ) ) + (retval * sizeof(UCHAR)))) # UChar  |-> (Znth retval table 0))
  **  (UCharArray.missing_i ( &( "shift" ) ) retval 0 256 table )
  **  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
.

Definition horspool_memmem_refinement_partial_solve_wit_10_pure :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (m1 >= 15)) (PreH2 : (tmp >= m1)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : (ne_len_pre <= hs_len_pre)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH17 : (ne = needle_pre)) (PreH18 : (m1 = (ne_len_pre - 1 ))) (PreH19 : (2 <= m1)) (PreH20 : (m1 <= 255)) (PreH21 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH22 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH23 : (1 <= shift1)) (PreH24 : (shift1 <= m1)) (PreH25 : (hp_filter_offset m1 offset )) (PreH26 : (0 <= position)) (PreH27 : (position <= hs_len_pre)) (PreH28 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH29 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH30 : (0 <= tmp)) (PreH31 : (tmp <= m1)) (PreH32 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((hs + (offset * sizeof(UCHAR))) = (base_low_level_spec + (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) )) ”
  &&  “ ((ne + (offset * sizeof(UCHAR))) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ”
  &&  “ (0 <= 8) ”
  &&  “ (((needleoff_low_level_spec + offset ) + 8 ) <= length_low_level_spec) ”
  &&  “ (((hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) + 8 ) <= length_low_level_spec) ”
  &&  “ (0 <= (needleoff_low_level_spec + offset )) ”
  &&  “ (0 <= (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR)))) ”
  &&  “ ((needle_pre + (offset * sizeof(UCHAR))) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ”
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 >= 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((needle_pre + (offset * sizeof(UCHAR))) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ”
  &&  “ (0 <= (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR)))) ”
  &&  “ (((hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) + 8 ) <= length_low_level_spec) ”
  &&  “ (((needleoff_low_level_spec + offset ) + 8 ) <= length_low_level_spec) ”
  &&  “ ((needle_pre + (offset * sizeof(UCHAR))) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ”
).

Definition horspool_memmem_refinement_partial_solve_wit_10_pure_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 >= 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((needle_pre + (offset * sizeof(UCHAR))) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_10_pure_split_goal_2 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 >= 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (0 <= (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR)))) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_10_pure_split_goal_3 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 >= 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (((hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) + 8 ) <= length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_10_pure_split_goal_4 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 >= 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (((needleoff_low_level_spec + offset ) + 8 ) <= length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_10_pure_split_goal_5 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 >= 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ ((needle_pre + (offset * sizeof(UCHAR))) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_10_aux :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (m1 >= 15)) (PreH2 : (tmp >= m1)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : (ne_len_pre <= hs_len_pre)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH17 : (ne = needle_pre)) (PreH18 : (m1 = (ne_len_pre - 1 ))) (PreH19 : (2 <= m1)) (PreH20 : (m1 <= 255)) (PreH21 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH22 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH23 : (1 <= shift1)) (PreH24 : (shift1 <= m1)) (PreH25 : (hp_filter_offset m1 offset )) (PreH26 : (0 <= position)) (PreH27 : (position <= hs_len_pre)) (PreH28 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH29 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH30 : (0 <= tmp)) (PreH31 : (tmp <= m1)) (PreH32 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ ((hs + (offset * sizeof(UCHAR))) = (base_low_level_spec + (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) )) ”
  &&  “ ((ne + (offset * sizeof(UCHAR))) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ”
  &&  “ (0 <= 8) ”
  &&  “ (((needleoff_low_level_spec + offset ) + 8 ) <= length_low_level_spec) ”
  &&  “ (((hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) + 8 ) <= length_low_level_spec) ”
  &&  “ (0 <= (needleoff_low_level_spec + offset )) ”
  &&  “ (0 <= (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR)))) ”
  &&  “ ((needle_pre + (offset * sizeof(UCHAR))) = (base_low_level_spec + (needleoff_low_level_spec + offset ) )) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_10 := horspool_memmem_refinement_partial_solve_wit_10_pure -> horspool_memmem_refinement_partial_solve_wit_10_aux.

Definition horspool_memmem_refinement_partial_solve_wit_11_pure :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (m1 < 15)) (PreH2 : (tmp >= m1)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : (ne_len_pre <= hs_len_pre)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH17 : (ne = needle_pre)) (PreH18 : (m1 = (ne_len_pre - 1 ))) (PreH19 : (2 <= m1)) (PreH20 : (m1 <= 255)) (PreH21 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH22 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH23 : (1 <= shift1)) (PreH24 : (shift1 <= m1)) (PreH25 : (hp_filter_offset m1 offset )) (PreH26 : (0 <= position)) (PreH27 : (position <= hs_len_pre)) (PreH28 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH29 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH30 : (0 <= tmp)) (PreH31 : (tmp <= m1)) (PreH32 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (hs = (base_low_level_spec + (hs + ((-base_low_level_spec) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base_low_level_spec + needleoff_low_level_spec )) ”
  &&  “ (0 <= needleoff_low_level_spec) ”
  &&  “ (0 <= m1) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + m1 ) <= length_low_level_spec) ”
  &&  “ ((needleoff_low_level_spec + m1 ) <= length_low_level_spec) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
  &&  “ (0 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
  &&  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 < 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
  &&  “ (0 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
  &&  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
).

Definition horspool_memmem_refinement_partial_solve_wit_11_pure_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 < 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_11_pure_split_goal_2 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 < 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (0 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_11_pure_split_goal_3 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 < 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_11_pure_split_goal_4 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 < 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_11_pure_split_goal_5 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (m1 < 15)) (PreH14 : (tmp >= m1)) (PreH15 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH16 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH17 : (0 < base_low_level_spec)) (PreH18 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH19 : (0 <= hayoff_low_level_spec)) (PreH20 : (0 <= needleoff_low_level_spec)) (PreH21 : (3 <= ne_len_pre)) (PreH22 : (ne_len_pre <= 256)) (PreH23 : (ne_len_pre <= hs_len_pre)) (PreH24 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH25 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH26 : (length_low_level_spec <= INT_MAX)) (PreH27 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH28 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH29 : (ne = needle_pre)) (PreH30 : (m1 = (ne_len_pre - 1 ))) (PreH31 : (2 <= m1)) (PreH32 : (m1 <= 255)) (PreH33 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH34 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH35 : (1 <= shift1)) (PreH36 : (shift1 <= m1)) (PreH37 : (hp_filter_offset m1 offset )) (PreH38 : (0 <= position)) (PreH39 : (position <= hs_len_pre)) (PreH40 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH41 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH42 : (0 <= tmp)) (PreH43 : (tmp <= m1)) (PreH44 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  ((( &( "haystack" ) )) # Ptr  |-> haystack_pre)
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
  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_11_aux :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (PreH1 : (m1 < 15)) (PreH2 : (tmp >= m1)) (PreH3 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH4 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH5 : (0 < base_low_level_spec)) (PreH6 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH7 : (0 <= hayoff_low_level_spec)) (PreH8 : (0 <= needleoff_low_level_spec)) (PreH9 : (3 <= ne_len_pre)) (PreH10 : (ne_len_pre <= 256)) (PreH11 : (ne_len_pre <= hs_len_pre)) (PreH12 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH13 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH14 : (length_low_level_spec <= INT_MAX)) (PreH15 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH16 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH17 : (ne = needle_pre)) (PreH18 : (m1 = (ne_len_pre - 1 ))) (PreH19 : (2 <= m1)) (PreH20 : (m1 <= 255)) (PreH21 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH22 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH23 : (1 <= shift1)) (PreH24 : (shift1 <= m1)) (PreH25 : (hp_filter_offset m1 offset )) (PreH26 : (0 <= position)) (PreH27 : (position <= hs_len_pre)) (PreH28 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH29 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH30 : (0 <= tmp)) (PreH31 : (tmp <= m1)) (PreH32 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (hs = (base_low_level_spec + (hs + ((-base_low_level_spec) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base_low_level_spec + needleoff_low_level_spec )) ”
  &&  “ (0 <= needleoff_low_level_spec) ”
  &&  “ (0 <= m1) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + m1 ) <= length_low_level_spec) ”
  &&  “ ((needleoff_low_level_spec + m1 ) <= length_low_level_spec) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
  &&  “ (0 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
  &&  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_11 := horspool_memmem_refinement_partial_solve_wit_11_pure -> horspool_memmem_refinement_partial_solve_wit_11_aux.

Definition horspool_memmem_refinement_partial_solve_wit_12_pure :=
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH3 : (INT_MIN <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (m1 >= 15)) (PreH6 : (tmp >= m1)) (PreH7 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (0 < base_low_level_spec)) (PreH10 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH11 : (0 <= hayoff_low_level_spec)) (PreH12 : (0 <= needleoff_low_level_spec)) (PreH13 : (3 <= ne_len_pre)) (PreH14 : (ne_len_pre <= 256)) (PreH15 : (ne_len_pre <= hs_len_pre)) (PreH16 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH17 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH18 : (length_low_level_spec <= INT_MAX)) (PreH19 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH20 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH21 : (ne = needle_pre)) (PreH22 : (m1 = (ne_len_pre - 1 ))) (PreH23 : (2 <= m1)) (PreH24 : (m1 <= 255)) (PreH25 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH26 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH27 : (1 <= shift1)) (PreH28 : (shift1 <= m1)) (PreH29 : (hp_filter_offset m1 offset )) (PreH30 : (0 <= position)) (PreH31 : (position <= hs_len_pre)) (PreH32 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH33 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH34 : (0 <= tmp)) (PreH35 : (tmp <= m1)) (PreH36 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
  “ (hs = (base_low_level_spec + (hs + ((-base_low_level_spec) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base_low_level_spec + needleoff_low_level_spec )) ”
  &&  “ (0 <= needleoff_low_level_spec) ”
  &&  “ (0 <= m1) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + m1 ) <= length_low_level_spec) ”
  &&  “ ((needleoff_low_level_spec + m1 ) <= length_low_level_spec) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
  &&  “ (0 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
  &&  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
) \/
(
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (retval = 0)) (PreH14 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH15 : (INT_MIN <= retval)) (PreH16 : (retval <= INT_MAX)) (PreH17 : (m1 >= 15)) (PreH18 : (tmp >= m1)) (PreH19 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH20 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH21 : (0 < base_low_level_spec)) (PreH22 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH23 : (0 <= hayoff_low_level_spec)) (PreH24 : (0 <= needleoff_low_level_spec)) (PreH25 : (3 <= ne_len_pre)) (PreH26 : (ne_len_pre <= 256)) (PreH27 : (ne_len_pre <= hs_len_pre)) (PreH28 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH29 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH30 : (length_low_level_spec <= INT_MAX)) (PreH31 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH32 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH33 : (ne = needle_pre)) (PreH34 : (m1 = (ne_len_pre - 1 ))) (PreH35 : (2 <= m1)) (PreH36 : (m1 <= 255)) (PreH37 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH39 : (1 <= shift1)) (PreH40 : (shift1 <= m1)) (PreH41 : (hp_filter_offset m1 offset )) (PreH42 : (0 <= position)) (PreH43 : (position <= hs_len_pre)) (PreH44 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH45 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH46 : (0 <= tmp)) (PreH47 : (tmp <= m1)) (PreH48 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
  &&  “ (0 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
  &&  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
).

Definition horspool_memmem_refinement_partial_solve_wit_12_pure_split_goal_1 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (retval = 0)) (PreH14 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH15 : (INT_MIN <= retval)) (PreH16 : (retval <= INT_MAX)) (PreH17 : (m1 >= 15)) (PreH18 : (tmp >= m1)) (PreH19 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH20 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH21 : (0 < base_low_level_spec)) (PreH22 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH23 : (0 <= hayoff_low_level_spec)) (PreH24 : (0 <= needleoff_low_level_spec)) (PreH25 : (3 <= ne_len_pre)) (PreH26 : (ne_len_pre <= 256)) (PreH27 : (ne_len_pre <= hs_len_pre)) (PreH28 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH29 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH30 : (length_low_level_spec <= INT_MAX)) (PreH31 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH32 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH33 : (ne = needle_pre)) (PreH34 : (m1 = (ne_len_pre - 1 ))) (PreH35 : (2 <= m1)) (PreH36 : (m1 <= 255)) (PreH37 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH39 : (1 <= shift1)) (PreH40 : (shift1 <= m1)) (PreH41 : (hp_filter_offset m1 offset )) (PreH42 : (0 <= position)) (PreH43 : (position <= hs_len_pre)) (PreH44 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH45 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH46 : (0 <= tmp)) (PreH47 : (tmp <= m1)) (PreH48 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_12_pure_split_goal_2 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (retval = 0)) (PreH14 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH15 : (INT_MIN <= retval)) (PreH16 : (retval <= INT_MAX)) (PreH17 : (m1 >= 15)) (PreH18 : (tmp >= m1)) (PreH19 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH20 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH21 : (0 < base_low_level_spec)) (PreH22 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH23 : (0 <= hayoff_low_level_spec)) (PreH24 : (0 <= needleoff_low_level_spec)) (PreH25 : (3 <= ne_len_pre)) (PreH26 : (ne_len_pre <= 256)) (PreH27 : (ne_len_pre <= hs_len_pre)) (PreH28 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH29 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH30 : (length_low_level_spec <= INT_MAX)) (PreH31 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH32 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH33 : (ne = needle_pre)) (PreH34 : (m1 = (ne_len_pre - 1 ))) (PreH35 : (2 <= m1)) (PreH36 : (m1 <= 255)) (PreH37 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH39 : (1 <= shift1)) (PreH40 : (shift1 <= m1)) (PreH41 : (hp_filter_offset m1 offset )) (PreH42 : (0 <= position)) (PreH43 : (position <= hs_len_pre)) (PreH44 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH45 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH46 : (0 <= tmp)) (PreH47 : (tmp <= m1)) (PreH48 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
  “ (0 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_12_pure_split_goal_3 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (retval = 0)) (PreH14 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH15 : (INT_MIN <= retval)) (PreH16 : (retval <= INT_MAX)) (PreH17 : (m1 >= 15)) (PreH18 : (tmp >= m1)) (PreH19 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH20 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH21 : (0 < base_low_level_spec)) (PreH22 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH23 : (0 <= hayoff_low_level_spec)) (PreH24 : (0 <= needleoff_low_level_spec)) (PreH25 : (3 <= ne_len_pre)) (PreH26 : (ne_len_pre <= 256)) (PreH27 : (ne_len_pre <= hs_len_pre)) (PreH28 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH29 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH30 : (length_low_level_spec <= INT_MAX)) (PreH31 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH32 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH33 : (ne = needle_pre)) (PreH34 : (m1 = (ne_len_pre - 1 ))) (PreH35 : (2 <= m1)) (PreH36 : (m1 <= 255)) (PreH37 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH39 : (1 <= shift1)) (PreH40 : (shift1 <= m1)) (PreH41 : (hp_filter_offset m1 offset )) (PreH42 : (0 <= position)) (PreH43 : (position <= hs_len_pre)) (PreH44 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH45 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH46 : (0 <= tmp)) (PreH47 : (tmp <= m1)) (PreH48 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_12_pure_split_goal_4 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (retval = 0)) (PreH14 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH15 : (INT_MIN <= retval)) (PreH16 : (retval <= INT_MAX)) (PreH17 : (m1 >= 15)) (PreH18 : (tmp >= m1)) (PreH19 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH20 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH21 : (0 < base_low_level_spec)) (PreH22 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH23 : (0 <= hayoff_low_level_spec)) (PreH24 : (0 <= needleoff_low_level_spec)) (PreH25 : (3 <= ne_len_pre)) (PreH26 : (ne_len_pre <= 256)) (PreH27 : (ne_len_pre <= hs_len_pre)) (PreH28 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH29 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH30 : (length_low_level_spec <= INT_MAX)) (PreH31 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH32 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH33 : (ne = needle_pre)) (PreH34 : (m1 = (ne_len_pre - 1 ))) (PreH35 : (2 <= m1)) (PreH36 : (m1 <= 255)) (PreH37 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH39 : (1 <= shift1)) (PreH40 : (shift1 <= m1)) (PreH41 : (hp_filter_offset m1 offset )) (PreH42 : (0 <= position)) (PreH43 : (position <= hs_len_pre)) (PreH44 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH45 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH46 : (0 <= tmp)) (PreH47 : (tmp <= m1)) (PreH48 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_12_pure_split_goal_5 :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (tmp <= UINT64_MAX)) (PreH2 : (offset <= UINT64_MAX)) (PreH3 : (shift1 <= UINT64_MAX)) (PreH4 : (m1 <= UINT64_MAX)) (PreH5 : (ne_len_pre <= UINT64_MAX)) (PreH6 : (hs_len_pre <= UINT64_MAX)) (PreH7 : (tmp >= 0)) (PreH8 : (offset >= 0)) (PreH9 : (shift1 >= 0)) (PreH10 : (m1 >= 0)) (PreH11 : (ne_len_pre >= 0)) (PreH12 : (hs_len_pre >= 0)) (PreH13 : (retval = 0)) (PreH14 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH15 : (INT_MIN <= retval)) (PreH16 : (retval <= INT_MAX)) (PreH17 : (m1 >= 15)) (PreH18 : (tmp >= m1)) (PreH19 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH20 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH21 : (0 < base_low_level_spec)) (PreH22 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH23 : (0 <= hayoff_low_level_spec)) (PreH24 : (0 <= needleoff_low_level_spec)) (PreH25 : (3 <= ne_len_pre)) (PreH26 : (ne_len_pre <= 256)) (PreH27 : (ne_len_pre <= hs_len_pre)) (PreH28 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH29 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH30 : (length_low_level_spec <= INT_MAX)) (PreH31 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH32 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH33 : (ne = needle_pre)) (PreH34 : (m1 = (ne_len_pre - 1 ))) (PreH35 : (2 <= m1)) (PreH36 : (m1 <= 255)) (PreH37 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH38 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH39 : (1 <= shift1)) (PreH40 : (shift1 <= m1)) (PreH41 : (hp_filter_offset m1 offset )) (PreH42 : (0 <= position)) (PreH43 : (position <= hs_len_pre)) (PreH44 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH45 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH46 : (0 <= tmp)) (PreH47 : (tmp <= m1)) (PreH48 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
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
  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
.

Definition horspool_memmem_refinement_partial_solve_wit_12_aux :=
forall (X_low_level_spec: ((@option Z) -> (unit -> Prop))) (needleoff_low_level_spec: Z) (hayoff_low_level_spec: Z) (bytes_low_level_spec: (@list Z)) (length_low_level_spec: Z) (base_low_level_spec: Z) (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (table: (@list Z)) (position: Z) (ne: Z) (m1: Z) (search_end: Z) (shift1: Z) (offset: Z) (hs: Z) (tmp: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval )) (PreH3 : (INT_MIN <= retval)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (m1 >= 15)) (PreH6 : (tmp >= m1)) (PreH7 : (haystack_pre = (base_low_level_spec + (hayoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH8 : (needle_pre = (base_low_level_spec + (needleoff_low_level_spec * sizeof(UCHAR) ) ))) (PreH9 : (0 < base_low_level_spec)) (PreH10 : ((base_low_level_spec + length_low_level_spec ) <= UINT_MAX)) (PreH11 : (0 <= hayoff_low_level_spec)) (PreH12 : (0 <= needleoff_low_level_spec)) (PreH13 : (3 <= ne_len_pre)) (PreH14 : (ne_len_pre <= 256)) (PreH15 : (ne_len_pre <= hs_len_pre)) (PreH16 : ((hayoff_low_level_spec + hs_len_pre ) <= length_low_level_spec)) (PreH17 : ((needleoff_low_level_spec + ne_len_pre ) <= length_low_level_spec)) (PreH18 : (length_low_level_spec <= INT_MAX)) (PreH19 : (hp_inputs bytes_low_level_spec length_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre )) (PreH20 : (safeExec ATrue (hp_search_from (bytes_low_level_spec) (hayoff_low_level_spec) (hs_len_pre) (needleoff_low_level_spec) (ne_len_pre) (position)) X_low_level_spec )) (PreH21 : (ne = needle_pre)) (PreH22 : (m1 = (ne_len_pre - 1 ))) (PreH23 : (2 <= m1)) (PreH24 : (m1 <= 255)) (PreH25 : (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1)))) (PreH26 : (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 )) (PreH27 : (1 <= shift1)) (PreH28 : (shift1 <= m1)) (PreH29 : (hp_filter_offset m1 offset )) (PreH30 : (0 <= position)) (PreH31 : (position <= hs_len_pre)) (PreH32 : (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1)))) (PreH33 : (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position )) (PreH34 : (0 <= tmp)) (PreH35 : (tmp <= m1)) (PreH36 : ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 ))))))),
  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
|--
  “ (hs = (base_low_level_spec + (hs + ((-base_low_level_spec) * sizeof(UCHAR))) )) ”
  &&  “ (ne = (base_low_level_spec + needleoff_low_level_spec )) ”
  &&  “ (0 <= needleoff_low_level_spec) ”
  &&  “ (0 <= m1) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + m1 ) <= length_low_level_spec) ”
  &&  “ ((needleoff_low_level_spec + m1 ) <= length_low_level_spec) ”
  &&  “ (((hs + ((-base_low_level_spec) * sizeof(UCHAR))) + (ne_len_pre - 1 ) ) <= length_low_level_spec) ”
  &&  “ (0 <= (hs + ((-base_low_level_spec) * sizeof(UCHAR)))) ”
  &&  “ (needle_pre = (base_low_level_spec + needleoff_low_level_spec )) ”
  &&  “ (retval = 0) ”
  &&  “ (hp_memcmp_result bytes_low_level_spec (hs + (((-base_low_level_spec) + offset ) * sizeof(UCHAR))) (needleoff_low_level_spec + offset ) 8 retval ) ”
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
  &&  “ (search_end = (haystack_pre + (((hs_len_pre - ne_len_pre ) * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_table_final bytes_low_level_spec needleoff_low_level_spec ne_len_pre table shift1 ) ”
  &&  “ (1 <= shift1) ”
  &&  “ (shift1 <= m1) ”
  &&  “ (hp_filter_offset m1 offset ) ”
  &&  “ (0 <= position) ”
  &&  “ (position <= hs_len_pre) ”
  &&  “ (hs = (haystack_pre + ((position * sizeof(UCHAR) ) * 1))) ”
  &&  “ (hp_no_match_before bytes_low_level_spec hayoff_low_level_spec hs_len_pre needleoff_low_level_spec ne_len_pre position ) ”
  &&  “ (0 <= tmp) ”
  &&  “ (tmp <= m1) ”
  &&  “ ((tmp = m1) -> (((position + ne_len_pre ) <= hs_len_pre) /\ ((hp_hash_at (bytes_low_level_spec) (((hayoff_low_level_spec + position ) + m1 ))) = (hp_hash_at (bytes_low_level_spec) ((needleoff_low_level_spec + m1 )))))) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec )
  **  (UCharArray.full ( &( "shift" ) ) 256 table )
.

Definition horspool_memmem_refinement_partial_solve_wit_12 := horspool_memmem_refinement_partial_solve_wit_12_pure -> horspool_memmem_refinement_partial_solve_wit_12_aux.

(* Shallow FunAssertion specs for horspool_memmem_refinement. *)
Definition horspool_memmem_refinement_sig : FuncSig := ([ * void; u64;  * void; u64],  * void)%ctype.

Definition horspool_memmem_refinement_low_level_spec : Spec horspool_memmem_refinement_sig :=
  fun F =>
ALL (base: Z),
ALL (length: Z),
ALL (bytes: (@list Z)),
ALL (hayoff: Z),
ALL (needleoff: Z),
ALL (X: ((@option Z) -> (unit -> Prop))),
HoareFun ([ * void; u64;  * void; u64],  * void)%ctype
  (fun '(haystack_pre, (hs_len_pre, (needle_pre, ne_len_pre))) =>
  (“ (haystack_pre = (base + (hayoff * sizeof(UCHAR) ) )) ”
  &&  “ (needle_pre = (base + (needleoff * sizeof(UCHAR) ) )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (0 <= hayoff) ”
  &&  “ (0 <= needleoff) ”
  &&  “ (0 <= hs_len_pre) ”
  &&  “ (3 <= ne_len_pre) ”
  &&  “ (ne_len_pre <= 256) ”
  &&  “ ((hayoff + hs_len_pre ) <= length) ”
  &&  “ ((needleoff + ne_len_pre ) <= length) ”
  &&  “ (length <= INT_MAX) ”
  &&  “ (hp_inputs bytes length hayoff hs_len_pre needleoff ne_len_pre ) ”
  &&  “ (safeExec ATrue (hp_search_from (bytes) (hayoff) (hs_len_pre) (needleoff) (ne_len_pre) (0)) X ) ”
  &&  (UCharArray.full base length bytes )))
  (fun '(haystack_pre, (hs_len_pre, (needle_pre, ne_len_pre))) retval =>
  (“ (safeExec ATrue (return ((hp_ptr_result ((base + hayoff )) (retval)))) X ) ”
  &&  (UCharArray.full base length bytes )))
  F.

Definition horspool_memmem_refinement_high_level_spec : Spec horspool_memmem_refinement_sig :=
  fun F =>
ALL (base: Z),
ALL (length: Z),
ALL (bytes: (@list Z)),
ALL (hayoff: Z),
ALL (needleoff: Z),
HoareFun ([ * void; u64;  * void; u64],  * void)%ctype
  (fun '(haystack_pre, (hs_len_pre, (needle_pre, ne_len_pre))) =>
  (“ (haystack_pre = (base + (hayoff * sizeof(UCHAR) ) )) ”
  &&  “ (needle_pre = (base + (needleoff * sizeof(UCHAR) ) )) ”
  &&  “ (0 < base) ”
  &&  “ ((base + length ) <= UINT_MAX) ”
  &&  “ (0 <= hayoff) ”
  &&  “ (0 <= needleoff) ”
  &&  “ (0 <= hs_len_pre) ”
  &&  “ (3 <= ne_len_pre) ”
  &&  “ (ne_len_pre <= 256) ”
  &&  “ ((hayoff + hs_len_pre ) <= length) ”
  &&  “ ((needleoff + ne_len_pre ) <= length) ”
  &&  “ (length <= INT_MAX) ”
  &&  “ (hp_inputs bytes length hayoff hs_len_pre needleoff ne_len_pre ) ”
  &&  (UCharArray.full base length bytes )))
  (fun '(haystack_pre, (hs_len_pre, (needle_pre, ne_len_pre))) retval =>
  (“ (hp_result bytes base hayoff hs_len_pre needleoff ne_len_pre retval ) ”
  &&  (UCharArray.full base length bytes )))
  F.

Definition horspool_memmem_refinement_low_level_spec_entail_high_level_spec :=
forall (haystack_pre: Z) (hs_len_pre: Z) (needle_pre: Z) (ne_len_pre: Z) (base_high_level_spec: Z) (length_high_level_spec: Z) (bytes_high_level_spec: (@list Z)) (hayoff_high_level_spec: Z) (needleoff_high_level_spec: Z),
  (“ (haystack_pre = (base_high_level_spec + (hayoff_high_level_spec * sizeof(UCHAR) ) )) ”
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
  &&  (UCharArray.full base_high_level_spec length_high_level_spec bytes_high_level_spec ))
|--
EX (base_low_level_spec: Z)(length_low_level_spec: Z)(bytes_low_level_spec: (@list Z))(hayoff_low_level_spec: Z)(needleoff_low_level_spec: Z)(X_low_level_spec: ((@option Z) -> (unit -> Prop))),
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
  (ALL (retval: Z),
  (“ (safeExec ATrue (return ((hp_ptr_result ((base_low_level_spec + hayoff_low_level_spec )) (retval)))) X_low_level_spec ) ”
  &&  (UCharArray.full base_low_level_spec length_low_level_spec bytes_low_level_spec ))
  -*
  (“ (hp_result bytes_high_level_spec base_high_level_spec hayoff_high_level_spec hs_len_pre needleoff_high_level_spec ne_len_pre retval ) ”
  &&  (UCharArray.full base_high_level_spec length_high_level_spec bytes_high_level_spec )))
.

Module Type VC_Correct.


Axiom proof_of_hp_hash2_safety_wit_1 : hp_hash2_safety_wit_1.
Axiom proof_of_hp_hash2_safety_wit_2 : hp_hash2_safety_wit_2.
Axiom proof_of_hp_hash2_safety_wit_3 : hp_hash2_safety_wit_3.
Axiom proof_of_hp_hash2_safety_wit_4 : hp_hash2_safety_wit_4.
Axiom proof_of_hp_hash2_safety_wit_5 : hp_hash2_safety_wit_5.
Axiom proof_of_hp_hash2_safety_wit_6 : hp_hash2_safety_wit_6.
Axiom proof_of_hp_hash2_safety_wit_7 : hp_hash2_safety_wit_7.
Axiom proof_of_hp_hash2_entail_wit_1 : hp_hash2_entail_wit_1.
Axiom proof_of_hp_hash2_return_wit_1 : hp_hash2_return_wit_1.
Axiom proof_of_hp_hash2_partial_solve_wit_1 : hp_hash2_partial_solve_wit_1.
Axiom proof_of_hp_hash2_partial_solve_wit_2 : hp_hash2_partial_solve_wit_2.
Axiom proof_of_horspool_memmem_refinement_safety_wit_1 : horspool_memmem_refinement_safety_wit_1.
Axiom proof_of_horspool_memmem_refinement_safety_wit_2 : horspool_memmem_refinement_safety_wit_2.
Axiom proof_of_horspool_memmem_refinement_safety_wit_3 : horspool_memmem_refinement_safety_wit_3.
Axiom proof_of_horspool_memmem_refinement_safety_wit_4 : horspool_memmem_refinement_safety_wit_4.
Axiom proof_of_horspool_memmem_refinement_safety_wit_5 : horspool_memmem_refinement_safety_wit_5.
Axiom proof_of_horspool_memmem_refinement_safety_wit_6 : horspool_memmem_refinement_safety_wit_6.
Axiom proof_of_horspool_memmem_refinement_safety_wit_7 : horspool_memmem_refinement_safety_wit_7.
Axiom proof_of_horspool_memmem_refinement_safety_wit_8 : horspool_memmem_refinement_safety_wit_8.
Axiom proof_of_horspool_memmem_refinement_safety_wit_9 : horspool_memmem_refinement_safety_wit_9.
Axiom proof_of_horspool_memmem_refinement_safety_wit_10 : horspool_memmem_refinement_safety_wit_10.
Axiom proof_of_horspool_memmem_refinement_safety_wit_11 : horspool_memmem_refinement_safety_wit_11.
Axiom proof_of_horspool_memmem_refinement_safety_wit_12 : horspool_memmem_refinement_safety_wit_12.
Axiom proof_of_horspool_memmem_refinement_safety_wit_13 : horspool_memmem_refinement_safety_wit_13.
Axiom proof_of_horspool_memmem_refinement_safety_wit_14 : horspool_memmem_refinement_safety_wit_14.
Axiom proof_of_horspool_memmem_refinement_safety_wit_15 : horspool_memmem_refinement_safety_wit_15.
Axiom proof_of_horspool_memmem_refinement_safety_wit_16 : horspool_memmem_refinement_safety_wit_16.
Axiom proof_of_horspool_memmem_refinement_safety_wit_17 : horspool_memmem_refinement_safety_wit_17.
Axiom proof_of_horspool_memmem_refinement_safety_wit_18 : horspool_memmem_refinement_safety_wit_18.
Axiom proof_of_horspool_memmem_refinement_safety_wit_19 : horspool_memmem_refinement_safety_wit_19.
Axiom proof_of_horspool_memmem_refinement_safety_wit_20 : horspool_memmem_refinement_safety_wit_20.
Axiom proof_of_horspool_memmem_refinement_safety_wit_21 : horspool_memmem_refinement_safety_wit_21.
Axiom proof_of_horspool_memmem_refinement_safety_wit_22 : horspool_memmem_refinement_safety_wit_22.
Axiom proof_of_horspool_memmem_refinement_safety_wit_23 : horspool_memmem_refinement_safety_wit_23.
Axiom proof_of_horspool_memmem_refinement_entail_wit_1 : horspool_memmem_refinement_entail_wit_1.
Axiom proof_of_horspool_memmem_refinement_entail_wit_2 : horspool_memmem_refinement_entail_wit_2.
Axiom proof_of_horspool_memmem_refinement_entail_wit_3 : horspool_memmem_refinement_entail_wit_3.
Axiom proof_of_horspool_memmem_refinement_entail_wit_4 : horspool_memmem_refinement_entail_wit_4.
Axiom proof_of_horspool_memmem_refinement_entail_wit_5 : horspool_memmem_refinement_entail_wit_5.
Axiom proof_of_horspool_memmem_refinement_entail_wit_6 : horspool_memmem_refinement_entail_wit_6.
Axiom proof_of_horspool_memmem_refinement_entail_wit_7 : horspool_memmem_refinement_entail_wit_7.
Axiom proof_of_horspool_memmem_refinement_entail_wit_8_1 : horspool_memmem_refinement_entail_wit_8_1.
Axiom proof_of_horspool_memmem_refinement_entail_wit_8_2 : horspool_memmem_refinement_entail_wit_8_2.
Axiom proof_of_horspool_memmem_refinement_entail_wit_9_1 : horspool_memmem_refinement_entail_wit_9_1.
Axiom proof_of_horspool_memmem_refinement_entail_wit_9_2 : horspool_memmem_refinement_entail_wit_9_2.
Axiom proof_of_horspool_memmem_refinement_entail_wit_9_3 : horspool_memmem_refinement_entail_wit_9_3.
Axiom proof_of_horspool_memmem_refinement_entail_wit_9_4 : horspool_memmem_refinement_entail_wit_9_4.
Axiom proof_of_horspool_memmem_refinement_entail_wit_9_5 : horspool_memmem_refinement_entail_wit_9_5.
Axiom proof_of_horspool_memmem_refinement_entail_wit_10_1 : horspool_memmem_refinement_entail_wit_10_1.
Axiom proof_of_horspool_memmem_refinement_entail_wit_10_2 : horspool_memmem_refinement_entail_wit_10_2.
Axiom proof_of_horspool_memmem_refinement_return_wit_1 : horspool_memmem_refinement_return_wit_1.
Axiom proof_of_horspool_memmem_refinement_return_wit_2 : horspool_memmem_refinement_return_wit_2.
Axiom proof_of_horspool_memmem_refinement_return_wit_3 : horspool_memmem_refinement_return_wit_3.
Axiom proof_of_horspool_memmem_refinement_return_wit_4 : horspool_memmem_refinement_return_wit_4.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_1_pure : horspool_memmem_refinement_partial_solve_wit_1_pure.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_1 : horspool_memmem_refinement_partial_solve_wit_1.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_2_pure : horspool_memmem_refinement_partial_solve_wit_2_pure.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_2 : horspool_memmem_refinement_partial_solve_wit_2.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_3 : horspool_memmem_refinement_partial_solve_wit_3.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_4_pure : horspool_memmem_refinement_partial_solve_wit_4_pure.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_4 : horspool_memmem_refinement_partial_solve_wit_4.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_5 : horspool_memmem_refinement_partial_solve_wit_5.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_6_pure : horspool_memmem_refinement_partial_solve_wit_6_pure.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_6 : horspool_memmem_refinement_partial_solve_wit_6.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_7 : horspool_memmem_refinement_partial_solve_wit_7.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_8_pure : horspool_memmem_refinement_partial_solve_wit_8_pure.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_8 : horspool_memmem_refinement_partial_solve_wit_8.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_9 : horspool_memmem_refinement_partial_solve_wit_9.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_10_pure : horspool_memmem_refinement_partial_solve_wit_10_pure.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_10 : horspool_memmem_refinement_partial_solve_wit_10.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_11_pure : horspool_memmem_refinement_partial_solve_wit_11_pure.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_11 : horspool_memmem_refinement_partial_solve_wit_11.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_12_pure : horspool_memmem_refinement_partial_solve_wit_12_pure.
Axiom proof_of_horspool_memmem_refinement_partial_solve_wit_12 : horspool_memmem_refinement_partial_solve_wit_12.
Axiom proof_of_horspool_memmem_refinement_low_level_spec_entail_high_level_spec : horspool_memmem_refinement_low_level_spec_entail_high_level_spec.

End VC_Correct.
