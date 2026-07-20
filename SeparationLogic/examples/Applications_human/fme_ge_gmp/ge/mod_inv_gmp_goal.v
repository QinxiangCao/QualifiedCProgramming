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
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.ge.ge_gmp_lib.
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import ge_gmp_array_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.ge Require Import ge_gmp_array_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_strategy_proof.

(*----- Function mpz_odd_positive -----*)

Definition mpz_odd_positive_safety_wit_1 := 
forall (x_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) ,
  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((( &( "limb0" ) )) # UInt  |->_)
  **  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_odd_positive_safety_wit_2 := 
forall (x_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((( &( "limb0" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0))
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_odd_positive_safety_wit_3 := 
forall (x_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) <> 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((( &( "limb0" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0))
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_odd_positive_safety_wit_4 := 
forall (x_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) = 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((( &( "limb0" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0))
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_odd_positive_entail_wit_1 := 
(
forall (x_pre: Z) (z: Z) (PreH1 : (z > 0)) ,
  (store_Z x_pre z )
|--
  “ (z > 0) ”
  &&  (store_Z_read0 x_pre z )
) \/
(
forall (x_pre: Z) (z: Z) (PreH1 : (z > 0)) ,
  (store_Z x_pre z )
|--
  (store_Z_read0 x_pre z )
).

Definition mpz_odd_positive_entail_wit_1_split_goal_spatial := 
forall (x_pre: Z) (z: Z) (PreH1 : (z > 0)) ,
  (store_Z x_pre z )
|--
  (store_Z_read0 x_pre z )
.

Definition mpz_odd_positive_entail_wit_2 := 
(
forall (x_pre: Z) (z: Z) (PreH1 : (z > 0)) ,
  (store_Z_read0 x_pre z )
|--
  EX (ptr: Z)  (data: (@list Z))  (cap: Z)  (size: Z) ,
  “ (z > 0) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z size ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (data)) = (Zabs (z))) ” 
  &&  “ ((last (data) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD data ) ” 
  &&  “ ((Zlength (data)) = (Zabs (size))) ”
  &&  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
) \/
(
forall (z: Z) (ptr_2: Z) (size_2: Z) (cap_2: Z) (PreH1 : (same_sign z size_2 )) (PreH2 : ((Zabs (size_2)) <= cap_2)) (PreH3 : (z > 0)) ,
  (mpd_store_Z_compact_read0 ptr_2 (Zabs (z)) (Zabs (size_2)) )
|--
  EX (data: (@list Z)) ,
  “ (z > 0) ” 
  &&  “ ((Zabs (size_2)) <= cap_2) ” 
  &&  “ (same_sign z size_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (data)) = (Zabs (z))) ” 
  &&  “ ((last (data) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD data ) ” 
  &&  “ ((Zlength (data)) = (Zabs (size_2))) ”
  &&  (UIntArray.seg ptr_2 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr_2 1 (Zmax ((Zabs (size_2))) (1)) (sublist (1) ((Zmax ((Zabs (size_2))) (1))) ((mpd_read0_data (data)))) )
).

Definition mpz_odd_positive_return_wit_1 := 
(
forall (x_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) = 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ (0 = 0) ” 
  &&  “ ((z % ( 2 ) ) = 0) ”
  &&  (store_Z x_pre z )
) \/
(
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) = 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ ((z % ( 2 ) ) = 0) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z)) (Zabs (size)) )
).

Definition mpz_odd_positive_return_wit_1_split_goal_1 := 
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) = 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ ((z % ( 2 ) ) = 0) ”
.

Definition mpz_odd_positive_return_wit_1_split_goal_spatial := 
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) = 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z)) (Zabs (size)) )
.

Definition mpz_odd_positive_return_wit_2 := 
(
forall (x_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) <> 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ (1 = 1) ” 
  &&  “ ((z % ( 2 ) ) = 1) ”
  &&  (store_Z x_pre z )
) \/
(
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) <> 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ ((z % ( 2 ) ) = 1) ”
  &&  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z)) (Zabs (size)) )
).

Definition mpz_odd_positive_return_wit_2_split_goal_1 := 
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) <> 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ ((z % ( 2 ) ) = 1) ”
.

Definition mpz_odd_positive_return_wit_2_split_goal_spatial := 
forall (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) (PreH8 : ((Z.land (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0) 1) <> 0)) ,
  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z)) (Zabs (size)) )
.

Definition mpz_odd_positive_partial_solve_wit_1 := 
forall (x_pre: Z) (z: Z) (ptr: Z) (size: Z) (cap: Z) (data: (@list Z)) (PreH1 : (z > 0)) (PreH2 : ((Zabs (size)) <= cap)) (PreH3 : (same_sign z size )) (PreH4 : ((list_to_Z (UINT_MOD) (data)) = (Zabs (z)))) (PreH5 : ((last (data) (1)) >= 1)) (PreH6 : (list_within_bound UINT_MOD data )) (PreH7 : ((Zlength (data)) = (Zabs (size)))) ,
  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.seg ptr 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
|--
  “ (z > 0) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z size ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (data)) = (Zabs (z))) ” 
  &&  “ ((last (data) (1)) >= 1) ” 
  &&  “ (list_within_bound UINT_MOD data ) ” 
  &&  “ ((Zlength (data)) = (Zabs (size))) ”
  &&  (((ptr + (0 * sizeof(UINT)))) # UInt  |-> (Znth (0 - 0 ) (sublist (0) (1) ((mpd_read0_data (data)))) 0))
  **  (UIntArray.missing_i ptr 0 0 1 (sublist (0) (1) ((mpd_read0_data (data)))) )
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((x_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (UIntArray.seg ptr 1 (Zmax ((Zabs (size))) (1)) (sublist (1) ((Zmax ((Zabs (size))) (1))) ((mpd_read0_data (data)))) )
  **  (UIntArray.undef_seg ptr (Zmax ((Zabs (size))) (1)) cap )
.

(*----- Function mod_inv_gmp -----*)

Definition mod_inv_gmp_safety_wit_1 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 < za_low_level_spec)) (PreH10 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((( &( "odd" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_4)
  **  ((( &( "exp" ) )) # Ptr  |-> retval_3)
  **  ((( &( "base" ) )) # Ptr  |-> retval_2)
  **  ((( &( "result" ) )) # Ptr  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mod_inv_gmp_safety_wit_2 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH2 : (retval_4 <> 0)) (PreH3 : (retval_3 <> 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_3 zp_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  ((( &( "odd" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_4)
  **  ((( &( "exp" ) )) # Ptr  |-> retval_3)
  **  ((( &( "base" ) )) # Ptr  |-> retval_2)
  **  ((( &( "result" ) )) # Ptr  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z r_pre old_low_level_spec )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mod_inv_gmp_safety_wit_3 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (out: Z) (retval_5: Z) (PreH1 : ((zp_low_level_spec - 2 ) < 0)) (PreH2 : (retval_5 = (-1))) (PreH3 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval <> 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_3 (zp_low_level_spec - 2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  ((( &( "odd" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_4)
  **  ((( &( "exp" ) )) # Ptr  |-> retval_3)
  **  ((( &( "base" ) )) # Ptr  |-> retval_2)
  **  ((( &( "result" ) )) # Ptr  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z r_pre old_low_level_spec )
|--
  “ False ”
.

Definition mod_inv_gmp_safety_wit_4 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (result <> 0)) (PreH5 : (base <> 0)) (PreH6 : (exp <> 0)) (PreH7 : (tmp <> 0)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 < za_low_level_spec)) (PreH10 : (za_low_level_spec < zp_low_level_spec)) (PreH11 : (0 <= zresult)) (PreH12 : (zresult < zp_low_level_spec)) (PreH13 : (0 <= zbase)) (PreH14 : (zbase < zp_low_level_spec)) (PreH15 : (0 <= zexp)) (PreH16 : (same_sign s zexp )) (PreH17 : (mpz_div_qr_ret_ok s zexp )) (PreH18 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mod_inv_gmp_safety_wit_5 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((zexp % ( 2 ) ) = 1)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval = 0)) ,
  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
|--
  “ False ”
.

Definition mod_inv_gmp_safety_wit_6 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((zexp % ( 2 ) ) = 0)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval <> 0)) ,
  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
|--
  “ False ”
.

Definition mod_inv_gmp_safety_wit_7 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (out_2: Z) (PreH1 : (mod_norm_spec zp_low_level_spec (zbase * zbase ) out_2 )) (PreH2 : (mod_norm_spec zp_low_level_spec (zresult * zbase ) out )) (PreH3 : (retval = 1)) (PreH4 : ((zexp % ( 2 ) ) = 1)) (PreH5 : (s > 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (result <> 0)) (PreH10 : (base <> 0)) (PreH11 : (exp <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 < za_low_level_spec)) (PreH15 : (za_low_level_spec < zp_low_level_spec)) (PreH16 : (0 <= zresult)) (PreH17 : (zresult < zp_low_level_spec)) (PreH18 : (0 <= zbase)) (PreH19 : (zbase < zp_low_level_spec)) (PreH20 : (0 <= zexp)) (PreH21 : (same_sign s zexp )) (PreH22 : (mpz_div_qr_ret_ok s zexp )) (PreH23 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH24 : (retval <> 0)) ,
  (store_Z base out_2 )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mod_inv_gmp_safety_wit_8 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec (zbase * zbase ) out )) (PreH2 : (retval = 0)) (PreH3 : ((zexp % ( 2 ) ) = 0)) (PreH4 : (s > 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (result <> 0)) (PreH9 : (base <> 0)) (PreH10 : (exp <> 0)) (PreH11 : (tmp <> 0)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 < za_low_level_spec)) (PreH14 : (za_low_level_spec < zp_low_level_spec)) (PreH15 : (0 <= zresult)) (PreH16 : (zresult < zp_low_level_spec)) (PreH17 : (0 <= zbase)) (PreH18 : (zbase < zp_low_level_spec)) (PreH19 : (0 <= zexp)) (PreH20 : (same_sign s zexp )) (PreH21 : (mpz_div_qr_ret_ok s zexp )) (PreH22 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH23 : (retval = 0)) ,
  (store_Z base out )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mod_inv_gmp_entail_wit_1_1 := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (out: Z) (retval_5: Z) (PreH1 : ((zp_low_level_spec - 2 ) = 0)) (PreH2 : (retval_5 = 0)) (PreH3 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval <> 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_3 (zp_low_level_spec - 2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  (store_Z r_pre old_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval_5 zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval_5 zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval zresult )
  **  (store_Z retval_2 zbase )
  **  (store_Z retval_3 zexp )
  **  (store_Z retval_4 ztmp )
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (out: Z) (retval_5: Z) (PreH1 : ((zp_low_level_spec - 2 ) = 0)) (PreH2 : (retval_5 = 0)) (PreH3 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval <> 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_3 (zp_low_level_spec - 2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  (store_Z r_pre old_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval_5 zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval_5 zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval zresult )
  **  (store_Z retval_2 zbase )
  **  (store_Z retval_3 zexp )
  **  (store_Z retval_4 ztmp )
).

Definition mod_inv_gmp_entail_wit_1_2 := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (out: Z) (retval_5: Z) (PreH1 : ((zp_low_level_spec - 2 ) > 0)) (PreH2 : (retval_5 = 1)) (PreH3 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval <> 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_3 (zp_low_level_spec - 2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  (store_Z r_pre old_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval_5 zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval_5 zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval zresult )
  **  (store_Z retval_2 zbase )
  **  (store_Z retval_3 zexp )
  **  (store_Z retval_4 ztmp )
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (out: Z) (retval_5: Z) (PreH1 : ((zp_low_level_spec - 2 ) > 0)) (PreH2 : (retval_5 = 1)) (PreH3 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH4 : (retval_4 <> 0)) (PreH5 : (retval_3 <> 0)) (PreH6 : (retval_2 <> 0)) (PreH7 : (retval <> 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_3 (zp_low_level_spec - 2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  (store_Z r_pre old_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval_5 zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval_5 zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval zresult )
  **  (store_Z retval_2 zbase )
  **  (store_Z retval_3 zexp )
  **  (store_Z retval_4 ztmp )
).

Definition mod_inv_gmp_entail_wit_2_1 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((zexp % ( 2 ) ) = 1)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval = 0)) ,
  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
|--
  “ (retval = 0) ” 
  &&  “ ((zexp % ( 2 ) ) = 0) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
.

Definition mod_inv_gmp_entail_wit_2_2 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((zexp % ( 2 ) ) = 0)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval = 0)) ,
  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
|--
  “ (retval = 0) ” 
  &&  “ ((zexp % ( 2 ) ) = 0) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
.

Definition mod_inv_gmp_entail_wit_3_1 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((zexp % ( 2 ) ) = 1)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval <> 0)) ,
  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
|--
  “ (retval = 1) ” 
  &&  “ ((zexp % ( 2 ) ) = 1) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
.

Definition mod_inv_gmp_entail_wit_3_2 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((zexp % ( 2 ) ) = 0)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval <> 0)) ,
  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
|--
  “ (retval = 1) ” 
  &&  “ ((zexp % ( 2 ) ) = 1) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
.

Definition mod_inv_gmp_entail_wit_4_1 := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (out_2: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out_2 )) (PreH4 : (mod_norm_spec zp_low_level_spec (zresult_2 * zbase_2 ) out )) (PreH5 : (retval_2 = 1)) (PreH6 : ((zexp_2 % ( 2 ) ) = 1)) (PreH7 : (s > 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (result <> 0)) (PreH12 : (base <> 0)) (PreH13 : (exp <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 < za_low_level_spec)) (PreH17 : (za_low_level_spec < zp_low_level_spec)) (PreH18 : (0 <= zresult_2)) (PreH19 : (zresult_2 < zp_low_level_spec)) (PreH20 : (0 <= zbase_2)) (PreH21 : (zbase_2 < zp_low_level_spec)) (PreH22 : (0 <= zexp_2)) (PreH23 : (same_sign s zexp_2 )) (PreH24 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH25 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH26 : (retval_2 <> 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out_2 )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  ((( &( "odd" ) )) # Int  |-> retval_2)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (out_2: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out_2 )) (PreH4 : (mod_norm_spec zp_low_level_spec (zresult_2 * zbase_2 ) out )) (PreH5 : (retval_2 = 1)) (PreH6 : ((zexp_2 % ( 2 ) ) = 1)) (PreH7 : (s > 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (result <> 0)) (PreH12 : (base <> 0)) (PreH13 : (exp <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 < za_low_level_spec)) (PreH17 : (za_low_level_spec < zp_low_level_spec)) (PreH18 : (0 <= zresult_2)) (PreH19 : (zresult_2 < zp_low_level_spec)) (PreH20 : (0 <= zbase_2)) (PreH21 : (zbase_2 < zp_low_level_spec)) (PreH22 : (0 <= zexp_2)) (PreH23 : (same_sign s zexp_2 )) (PreH24 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH25 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH26 : (retval_2 <> 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out_2 )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
).

Definition mod_inv_gmp_entail_wit_4_2 := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (out_2: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) = 0)) (PreH2 : (retval = 0)) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out_2 )) (PreH4 : (mod_norm_spec zp_low_level_spec (zresult_2 * zbase_2 ) out )) (PreH5 : (retval_2 = 1)) (PreH6 : ((zexp_2 % ( 2 ) ) = 1)) (PreH7 : (s > 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (result <> 0)) (PreH12 : (base <> 0)) (PreH13 : (exp <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 < za_low_level_spec)) (PreH17 : (za_low_level_spec < zp_low_level_spec)) (PreH18 : (0 <= zresult_2)) (PreH19 : (zresult_2 < zp_low_level_spec)) (PreH20 : (0 <= zbase_2)) (PreH21 : (zbase_2 < zp_low_level_spec)) (PreH22 : (0 <= zexp_2)) (PreH23 : (same_sign s zexp_2 )) (PreH24 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH25 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH26 : (retval_2 <> 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out_2 )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  ((( &( "odd" ) )) # Int  |-> retval_2)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (out_2: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) = 0)) (PreH2 : (retval = 0)) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out_2 )) (PreH4 : (mod_norm_spec zp_low_level_spec (zresult_2 * zbase_2 ) out )) (PreH5 : (retval_2 = 1)) (PreH6 : ((zexp_2 % ( 2 ) ) = 1)) (PreH7 : (s > 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (result <> 0)) (PreH12 : (base <> 0)) (PreH13 : (exp <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 < za_low_level_spec)) (PreH17 : (za_low_level_spec < zp_low_level_spec)) (PreH18 : (0 <= zresult_2)) (PreH19 : (zresult_2 < zp_low_level_spec)) (PreH20 : (0 <= zbase_2)) (PreH21 : (zbase_2 < zp_low_level_spec)) (PreH22 : (0 <= zexp_2)) (PreH23 : (same_sign s zexp_2 )) (PreH24 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH25 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH26 : (retval_2 <> 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out_2 )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
).

Definition mod_inv_gmp_entail_wit_4_3 := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (out_2: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) > 0)) (PreH2 : (retval = 1)) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out_2 )) (PreH4 : (mod_norm_spec zp_low_level_spec (zresult_2 * zbase_2 ) out )) (PreH5 : (retval_2 = 1)) (PreH6 : ((zexp_2 % ( 2 ) ) = 1)) (PreH7 : (s > 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (result <> 0)) (PreH12 : (base <> 0)) (PreH13 : (exp <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 < za_low_level_spec)) (PreH17 : (za_low_level_spec < zp_low_level_spec)) (PreH18 : (0 <= zresult_2)) (PreH19 : (zresult_2 < zp_low_level_spec)) (PreH20 : (0 <= zbase_2)) (PreH21 : (zbase_2 < zp_low_level_spec)) (PreH22 : (0 <= zexp_2)) (PreH23 : (same_sign s zexp_2 )) (PreH24 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH25 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH26 : (retval_2 <> 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out_2 )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  ((( &( "odd" ) )) # Int  |-> retval_2)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (out_2: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) > 0)) (PreH2 : (retval = 1)) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out_2 )) (PreH4 : (mod_norm_spec zp_low_level_spec (zresult_2 * zbase_2 ) out )) (PreH5 : (retval_2 = 1)) (PreH6 : ((zexp_2 % ( 2 ) ) = 1)) (PreH7 : (s > 0)) (PreH8 : (r_pre <> 0)) (PreH9 : (a_pre <> 0)) (PreH10 : (p_pre <> 0)) (PreH11 : (result <> 0)) (PreH12 : (base <> 0)) (PreH13 : (exp <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (prime zp_low_level_spec )) (PreH16 : (0 < za_low_level_spec)) (PreH17 : (za_low_level_spec < zp_low_level_spec)) (PreH18 : (0 <= zresult_2)) (PreH19 : (zresult_2 < zp_low_level_spec)) (PreH20 : (0 <= zbase_2)) (PreH21 : (zbase_2 < zp_low_level_spec)) (PreH22 : (0 <= zexp_2)) (PreH23 : (same_sign s zexp_2 )) (PreH24 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH25 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH26 : (retval_2 <> 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out_2 )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
).

Definition mod_inv_gmp_entail_wit_4_4 := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out )) (PreH4 : (retval_2 = 0)) (PreH5 : ((zexp_2 % ( 2 ) ) = 0)) (PreH6 : (s > 0)) (PreH7 : (r_pre <> 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (result <> 0)) (PreH11 : (base <> 0)) (PreH12 : (exp <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 < za_low_level_spec)) (PreH16 : (za_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= zresult_2)) (PreH18 : (zresult_2 < zp_low_level_spec)) (PreH19 : (0 <= zbase_2)) (PreH20 : (zbase_2 < zp_low_level_spec)) (PreH21 : (0 <= zexp_2)) (PreH22 : (same_sign s zexp_2 )) (PreH23 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH24 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH25 : (retval_2 = 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  ((( &( "odd" ) )) # Int  |-> retval_2)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult_2 )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) < 0)) (PreH2 : (retval = (-1))) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out )) (PreH4 : (retval_2 = 0)) (PreH5 : ((zexp_2 % ( 2 ) ) = 0)) (PreH6 : (s > 0)) (PreH7 : (r_pre <> 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (result <> 0)) (PreH11 : (base <> 0)) (PreH12 : (exp <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 < za_low_level_spec)) (PreH16 : (za_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= zresult_2)) (PreH18 : (zresult_2 < zp_low_level_spec)) (PreH19 : (0 <= zbase_2)) (PreH20 : (zbase_2 < zp_low_level_spec)) (PreH21 : (0 <= zexp_2)) (PreH22 : (same_sign s zexp_2 )) (PreH23 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH24 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH25 : (retval_2 = 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult_2 )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
).

Definition mod_inv_gmp_entail_wit_4_5 := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) = 0)) (PreH2 : (retval = 0)) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out )) (PreH4 : (retval_2 = 0)) (PreH5 : ((zexp_2 % ( 2 ) ) = 0)) (PreH6 : (s > 0)) (PreH7 : (r_pre <> 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (result <> 0)) (PreH11 : (base <> 0)) (PreH12 : (exp <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 < za_low_level_spec)) (PreH16 : (za_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= zresult_2)) (PreH18 : (zresult_2 < zp_low_level_spec)) (PreH19 : (0 <= zbase_2)) (PreH20 : (zbase_2 < zp_low_level_spec)) (PreH21 : (0 <= zexp_2)) (PreH22 : (same_sign s zexp_2 )) (PreH23 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH24 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH25 : (retval_2 = 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  ((( &( "odd" ) )) # Int  |-> retval_2)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult_2 )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) = 0)) (PreH2 : (retval = 0)) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out )) (PreH4 : (retval_2 = 0)) (PreH5 : ((zexp_2 % ( 2 ) ) = 0)) (PreH6 : (s > 0)) (PreH7 : (r_pre <> 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (result <> 0)) (PreH11 : (base <> 0)) (PreH12 : (exp <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 < za_low_level_spec)) (PreH16 : (za_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= zresult_2)) (PreH18 : (zresult_2 < zp_low_level_spec)) (PreH19 : (0 <= zbase_2)) (PreH20 : (zbase_2 < zp_low_level_spec)) (PreH21 : (0 <= zexp_2)) (PreH22 : (same_sign s zexp_2 )) (PreH23 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH24 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH25 : (retval_2 = 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult_2 )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
).

Definition mod_inv_gmp_entail_wit_4_6 := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) > 0)) (PreH2 : (retval = 1)) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out )) (PreH4 : (retval_2 = 0)) (PreH5 : ((zexp_2 % ( 2 ) ) = 0)) (PreH6 : (s > 0)) (PreH7 : (r_pre <> 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (result <> 0)) (PreH11 : (base <> 0)) (PreH12 : (exp <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 < za_low_level_spec)) (PreH16 : (za_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= zresult_2)) (PreH18 : (zresult_2 < zp_low_level_spec)) (PreH19 : (0 <= zbase_2)) (PreH20 : (zbase_2 < zp_low_level_spec)) (PreH21 : (0 <= zexp_2)) (PreH22 : (same_sign s zexp_2 )) (PreH23 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH24 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH25 : (retval_2 = 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  ((( &( "odd" ) )) # Int  |-> retval_2)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult_2 )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp_2: Z) (zbase_2: Z) (zresult_2: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval_2: Z) (out: Z) (retval: Z) (PreH1 : ((Z.quot (zexp_2) ((Z.pow (2) (1)))) > 0)) (PreH2 : (retval = 1)) (PreH3 : (mod_norm_spec zp_low_level_spec (zbase_2 * zbase_2 ) out )) (PreH4 : (retval_2 = 0)) (PreH5 : ((zexp_2 % ( 2 ) ) = 0)) (PreH6 : (s > 0)) (PreH7 : (r_pre <> 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (result <> 0)) (PreH11 : (base <> 0)) (PreH12 : (exp <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 < za_low_level_spec)) (PreH16 : (za_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= zresult_2)) (PreH18 : (zresult_2 < zp_low_level_spec)) (PreH19 : (0 <= zbase_2)) (PreH20 : (zbase_2 < zp_low_level_spec)) (PreH21 : (0 <= zexp_2)) (PreH22 : (same_sign s zexp_2 )) (PreH23 : (mpz_div_qr_ret_ok s zexp_2 )) (PreH24 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult_2 zbase_2 zexp_2 )) (PreH25 : (retval_2 = 0)) ,
  (store_Z exp (Z.quot (zexp_2) ((Z.pow (2) (1)))) )
  **  (store_Z base out )
  **  (store_Z tmp (zbase_2 * zbase_2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult_2 )
|--
  EX (ztmp: Z)  (zexp: Z)  (zbase: Z)  (zresult: Z) ,
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign retval zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok retval zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
).

Definition mod_inv_gmp_return_wit_1 := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  (store_Z r_pre zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  EX (inv: Z) ,
  “ (mod_inverse_spec zp_low_level_spec za_low_level_spec inv ) ”
  &&  (store_Z r_pre inv )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  (store_Z r_pre zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  EX (inv: Z) ,
  “ (mod_inverse_spec zp_low_level_spec za_low_level_spec inv ) ”
  &&  (store_Z r_pre inv )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
).

Definition mod_inv_gmp_partial_solve_wit_1 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (PreH1 : (r_pre <> 0)) (PreH2 : (a_pre <> 0)) (PreH3 : (p_pre <> 0)) (PreH4 : (prime zp_low_level_spec )) (PreH5 : (0 < za_low_level_spec)) (PreH6 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_2 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (prime zp_low_level_spec )) (PreH6 : (0 < za_low_level_spec)) (PreH7 : (za_low_level_spec < zp_low_level_spec)) ,
  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_3 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (prime zp_low_level_spec )) (PreH6 : (0 < za_low_level_spec)) (PreH7 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_4 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (r_pre <> 0)) (PreH4 : (a_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (prime zp_low_level_spec )) (PreH7 : (0 < za_low_level_spec)) (PreH8 : (za_low_level_spec < zp_low_level_spec)) ,
  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_2)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_5 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (r_pre <> 0)) (PreH4 : (a_pre <> 0)) (PreH5 : (p_pre <> 0)) (PreH6 : (prime zp_low_level_spec )) (PreH7 : (0 < za_low_level_spec)) (PreH8 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_6 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (prime zp_low_level_spec )) (PreH8 : (0 < za_low_level_spec)) (PreH9 : (za_low_level_spec < zp_low_level_spec)) ,
  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_3)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_7 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (prime zp_low_level_spec )) (PreH8 : (0 < za_low_level_spec)) (PreH9 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_8 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 < za_low_level_spec)) (PreH10 : (za_low_level_spec < zp_low_level_spec)) ,
  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((retval_4)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |->_)
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_9_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 < za_low_level_spec)) (PreH10 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  ((( &( "odd" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_4)
  **  ((( &( "exp" ) )) # Ptr  |-> retval_3)
  **  ((( &( "base" ) )) # Ptr  |-> retval_2)
  **  ((( &( "result" ) )) # Ptr  |-> retval)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 = 1) ” 
  &&  “ (0 <= 1) ”
.

Definition mod_inv_gmp_partial_solve_wit_9_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 < za_low_level_spec)) (PreH10 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (1 = 1) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z retval 0 )
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_9 := mod_inv_gmp_partial_solve_wit_9_pure -> mod_inv_gmp_partial_solve_wit_9_aux.

Definition mod_inv_gmp_partial_solve_wit_10 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval <> 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 < za_low_level_spec)) (PreH10 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval 1 )
  **  (store_Z retval_4 0 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z retval_4 0 )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval_2 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_11_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 < za_low_level_spec)) (PreH10 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval_2 1 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval 0 )
  **  ((( &( "odd" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_4)
  **  ((( &( "exp" ) )) # Ptr  |-> retval_3)
  **  ((( &( "base" ) )) # Ptr  |-> retval)
  **  ((( &( "result" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ”
.

Definition mod_inv_gmp_partial_solve_wit_11_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval_2: Z) (retval: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (prime zp_low_level_spec )) (PreH9 : (0 < za_low_level_spec)) (PreH10 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval_2 1 )
  **  (store_Z retval_3 0 )
  **  (store_Z retval 0 )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (retval <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z retval 0 )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval_2 1 )
  **  (store_Z retval_3 0 )
  **  (store_Z r_pre old_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_11 := mod_inv_gmp_partial_solve_wit_11_pure -> mod_inv_gmp_partial_solve_wit_11_aux.

Definition mod_inv_gmp_partial_solve_wit_12 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH2 : (retval_4 <> 0)) (PreH3 : (retval_3 <> 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  (store_Z retval_3 0 )
  **  (store_Z r_pre old_low_level_spec )
|--
  “ (mod_norm_spec zp_low_level_spec za_low_level_spec out ) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z retval_3 0 )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  (store_Z r_pre old_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_13_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (retval_4: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH2 : (retval_4 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval zp_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_3 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval_2 1 )
  **  ((( &( "odd" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_4)
  **  ((( &( "exp" ) )) # Ptr  |-> retval)
  **  ((( &( "base" ) )) # Ptr  |-> retval_3)
  **  ((( &( "result" ) )) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (store_Z r_pre old_low_level_spec )
|--
  “ (retval = retval) ” 
  &&  “ (2 = 2) ” 
  &&  “ (0 <= 2) ”
.

Definition mod_inv_gmp_partial_solve_wit_13_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (retval_4: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH2 : (retval_4 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (retval_3 <> 0)) (PreH5 : (retval_2 <> 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval zp_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_3 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval_2 1 )
  **  (store_Z r_pre old_low_level_spec )
|--
  “ (retval = retval) ” 
  &&  “ (2 = 2) ” 
  &&  “ (0 <= 2) ” 
  &&  “ (mod_norm_spec zp_low_level_spec za_low_level_spec out ) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z retval zp_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_3 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval_2 1 )
  **  (store_Z r_pre old_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_13 := mod_inv_gmp_partial_solve_wit_13_pure -> mod_inv_gmp_partial_solve_wit_13_aux.

Definition mod_inv_gmp_partial_solve_wit_14 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec za_low_level_spec out )) (PreH2 : (retval_4 <> 0)) (PreH3 : (retval_3 <> 0)) (PreH4 : (retval_2 <> 0)) (PreH5 : (retval <> 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) ,
  (store_Z retval_3 (zp_low_level_spec - 2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  (store_Z r_pre old_low_level_spec )
|--
  “ (mod_norm_spec zp_low_level_spec za_low_level_spec out ) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ”
  &&  (store_Z retval_3 (zp_low_level_spec - 2 ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z retval_2 out )
  **  (store_Z retval_4 za_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z retval 1 )
  **  (store_Z r_pre old_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_15_pure := 
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s > 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
|--
  “ (zexp > 0) ”
) \/
(
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s <= INT_MAX)) (PreH2 : (s >= INT_MIN)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
|--
  “ (zexp > 0) ”
).

Definition mod_inv_gmp_partial_solve_wit_15_pure_split_goal_1 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s <= INT_MAX)) (PreH2 : (s >= INT_MIN)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |->_)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
|--
  “ (zexp > 0) ”
.

Definition mod_inv_gmp_partial_solve_wit_15_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s > 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
|--
  “ (zexp > 0) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
.

Definition mod_inv_gmp_partial_solve_wit_15 := mod_inv_gmp_partial_solve_wit_15_pure -> mod_inv_gmp_partial_solve_wit_15_aux.

Definition mod_inv_gmp_partial_solve_wit_16 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((zexp % ( 2 ) ) = 1)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval <> 0)) ,
  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
|--
  “ (retval = 1) ” 
  &&  “ ((zexp % ( 2 ) ) = 1) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_Z tmp ztmp )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_17_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((zexp % ( 2 ) ) = 1)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval <> 0)) ,
  (store_Z tmp (zresult * zbase ) )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (result <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ”
.

Definition mod_inv_gmp_partial_solve_wit_17_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 1)) (PreH2 : ((zexp % ( 2 ) ) = 1)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval <> 0)) ,
  (store_Z tmp (zresult * zbase ) )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (result <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((zexp % ( 2 ) ) = 1) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_Z result zresult )
  **  (store_Z tmp (zresult * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_17 := mod_inv_gmp_partial_solve_wit_17_pure -> mod_inv_gmp_partial_solve_wit_17_aux.

Definition mod_inv_gmp_partial_solve_wit_18 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec (zresult * zbase ) out )) (PreH2 : (retval = 1)) (PreH3 : ((zexp % ( 2 ) ) = 1)) (PreH4 : (s > 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (result <> 0)) (PreH9 : (base <> 0)) (PreH10 : (exp <> 0)) (PreH11 : (tmp <> 0)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 < za_low_level_spec)) (PreH14 : (za_low_level_spec < zp_low_level_spec)) (PreH15 : (0 <= zresult)) (PreH16 : (zresult < zp_low_level_spec)) (PreH17 : (0 <= zbase)) (PreH18 : (zbase < zp_low_level_spec)) (PreH19 : (0 <= zexp)) (PreH20 : (same_sign s zexp )) (PreH21 : (mpz_div_qr_ret_ok s zexp )) (PreH22 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH23 : (retval <> 0)) ,
  (store_Z result out )
  **  (store_Z tmp (zresult * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  “ (mod_norm_spec zp_low_level_spec (zresult * zbase ) out ) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((zexp % ( 2 ) ) = 1) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_Z tmp (zresult * zbase ) )
  **  (store_Z base zbase )
  **  (store_Z result out )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_19 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((zexp % ( 2 ) ) = 0)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval = 0)) ,
  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z tmp ztmp )
|--
  “ (retval = 0) ” 
  &&  “ ((zexp % ( 2 ) ) = 0) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z tmp ztmp )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
.

Definition mod_inv_gmp_partial_solve_wit_20_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec (zresult * zbase ) out )) (PreH2 : (retval = 1)) (PreH3 : ((zexp % ( 2 ) ) = 1)) (PreH4 : (s > 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (result <> 0)) (PreH9 : (base <> 0)) (PreH10 : (exp <> 0)) (PreH11 : (tmp <> 0)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 < za_low_level_spec)) (PreH14 : (za_low_level_spec < zp_low_level_spec)) (PreH15 : (0 <= zresult)) (PreH16 : (zresult < zp_low_level_spec)) (PreH17 : (0 <= zbase)) (PreH18 : (zbase < zp_low_level_spec)) (PreH19 : (0 <= zexp)) (PreH20 : (same_sign s zexp )) (PreH21 : (mpz_div_qr_ret_ok s zexp )) (PreH22 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH23 : (retval <> 0)) ,
  (store_Z tmp zbase )
  **  (store_Z base zbase )
  **  (store_Z result out )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  “ (tmp = tmp) ”
.

Definition mod_inv_gmp_partial_solve_wit_20_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec (zresult * zbase ) out )) (PreH2 : (retval = 1)) (PreH3 : ((zexp % ( 2 ) ) = 1)) (PreH4 : (s > 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (result <> 0)) (PreH9 : (base <> 0)) (PreH10 : (exp <> 0)) (PreH11 : (tmp <> 0)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 < za_low_level_spec)) (PreH14 : (za_low_level_spec < zp_low_level_spec)) (PreH15 : (0 <= zresult)) (PreH16 : (zresult < zp_low_level_spec)) (PreH17 : (0 <= zbase)) (PreH18 : (zbase < zp_low_level_spec)) (PreH19 : (0 <= zexp)) (PreH20 : (same_sign s zexp )) (PreH21 : (mpz_div_qr_ret_ok s zexp )) (PreH22 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH23 : (retval <> 0)) ,
  (store_Z tmp zbase )
  **  (store_Z base zbase )
  **  (store_Z result out )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  “ (tmp = tmp) ” 
  &&  “ (mod_norm_spec zp_low_level_spec (zresult * zbase ) out ) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((zexp % ( 2 ) ) = 1) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_Z tmp zbase )
  **  (store_Z base zbase )
  **  (store_Z result out )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_20 := mod_inv_gmp_partial_solve_wit_20_pure -> mod_inv_gmp_partial_solve_wit_20_aux.

Definition mod_inv_gmp_partial_solve_wit_21_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((zexp % ( 2 ) ) = 0)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval = 0)) ,
  (store_Z tmp zbase )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
|--
  “ (tmp = tmp) ”
.

Definition mod_inv_gmp_partial_solve_wit_21_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : ((zexp % ( 2 ) ) = 0)) (PreH3 : (s > 0)) (PreH4 : (r_pre <> 0)) (PreH5 : (a_pre <> 0)) (PreH6 : (p_pre <> 0)) (PreH7 : (result <> 0)) (PreH8 : (base <> 0)) (PreH9 : (exp <> 0)) (PreH10 : (tmp <> 0)) (PreH11 : (prime zp_low_level_spec )) (PreH12 : (0 < za_low_level_spec)) (PreH13 : (za_low_level_spec < zp_low_level_spec)) (PreH14 : (0 <= zresult)) (PreH15 : (zresult < zp_low_level_spec)) (PreH16 : (0 <= zbase)) (PreH17 : (zbase < zp_low_level_spec)) (PreH18 : (0 <= zexp)) (PreH19 : (same_sign s zexp )) (PreH20 : (mpz_div_qr_ret_ok s zexp )) (PreH21 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH22 : (retval = 0)) ,
  (store_Z tmp zbase )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
|--
  “ (tmp = tmp) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((zexp % ( 2 ) ) = 0) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z tmp zbase )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
.

Definition mod_inv_gmp_partial_solve_wit_21 := mod_inv_gmp_partial_solve_wit_21_pure -> mod_inv_gmp_partial_solve_wit_21_aux.

Definition mod_inv_gmp_partial_solve_wit_22_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (PreH1 : (tmp = tmp)) (PreH2 : (mod_norm_spec zp_low_level_spec (zresult * zbase ) out )) (PreH3 : (retval = 1)) (PreH4 : ((zexp % ( 2 ) ) = 1)) (PreH5 : (s > 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (result <> 0)) (PreH10 : (base <> 0)) (PreH11 : (exp <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 < za_low_level_spec)) (PreH15 : (za_low_level_spec < zp_low_level_spec)) (PreH16 : (0 <= zresult)) (PreH17 : (zresult < zp_low_level_spec)) (PreH18 : (0 <= zbase)) (PreH19 : (zbase < zp_low_level_spec)) (PreH20 : (0 <= zexp)) (PreH21 : (same_sign s zexp )) (PreH22 : (mpz_div_qr_ret_ok s zexp )) (PreH23 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH24 : (retval <> 0)) ,
  (store_Z tmp (zbase * zbase ) )
  **  (store_Z base zbase )
  **  (store_Z result out )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  “ (base <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ”
.

Definition mod_inv_gmp_partial_solve_wit_22_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (PreH1 : (tmp = tmp)) (PreH2 : (mod_norm_spec zp_low_level_spec (zresult * zbase ) out )) (PreH3 : (retval = 1)) (PreH4 : ((zexp % ( 2 ) ) = 1)) (PreH5 : (s > 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (result <> 0)) (PreH10 : (base <> 0)) (PreH11 : (exp <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 < za_low_level_spec)) (PreH15 : (za_low_level_spec < zp_low_level_spec)) (PreH16 : (0 <= zresult)) (PreH17 : (zresult < zp_low_level_spec)) (PreH18 : (0 <= zbase)) (PreH19 : (zbase < zp_low_level_spec)) (PreH20 : (0 <= zexp)) (PreH21 : (same_sign s zexp )) (PreH22 : (mpz_div_qr_ret_ok s zexp )) (PreH23 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH24 : (retval <> 0)) ,
  (store_Z tmp (zbase * zbase ) )
  **  (store_Z base zbase )
  **  (store_Z result out )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  “ (base <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (mod_norm_spec zp_low_level_spec (zresult * zbase ) out ) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((zexp % ( 2 ) ) = 1) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_Z base zbase )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_22 := mod_inv_gmp_partial_solve_wit_22_pure -> mod_inv_gmp_partial_solve_wit_22_aux.

Definition mod_inv_gmp_partial_solve_wit_23_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (tmp = tmp)) (PreH2 : (retval = 0)) (PreH3 : ((zexp % ( 2 ) ) = 0)) (PreH4 : (s > 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (result <> 0)) (PreH9 : (base <> 0)) (PreH10 : (exp <> 0)) (PreH11 : (tmp <> 0)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 < za_low_level_spec)) (PreH14 : (za_low_level_spec < zp_low_level_spec)) (PreH15 : (0 <= zresult)) (PreH16 : (zresult < zp_low_level_spec)) (PreH17 : (0 <= zbase)) (PreH18 : (zbase < zp_low_level_spec)) (PreH19 : (0 <= zexp)) (PreH20 : (same_sign s zexp )) (PreH21 : (mpz_div_qr_ret_ok s zexp )) (PreH22 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH23 : (retval = 0)) ,
  (store_Z tmp (zbase * zbase ) )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
|--
  “ (base <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ”
.

Definition mod_inv_gmp_partial_solve_wit_23_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (PreH1 : (tmp = tmp)) (PreH2 : (retval = 0)) (PreH3 : ((zexp % ( 2 ) ) = 0)) (PreH4 : (s > 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (result <> 0)) (PreH9 : (base <> 0)) (PreH10 : (exp <> 0)) (PreH11 : (tmp <> 0)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 < za_low_level_spec)) (PreH14 : (za_low_level_spec < zp_low_level_spec)) (PreH15 : (0 <= zresult)) (PreH16 : (zresult < zp_low_level_spec)) (PreH17 : (0 <= zbase)) (PreH18 : (zbase < zp_low_level_spec)) (PreH19 : (0 <= zexp)) (PreH20 : (same_sign s zexp )) (PreH21 : (mpz_div_qr_ret_ok s zexp )) (PreH22 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH23 : (retval = 0)) ,
  (store_Z tmp (zbase * zbase ) )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
|--
  “ (base <> 0) ” 
  &&  “ (zp_low_level_spec > 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((zexp % ( 2 ) ) = 0) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z base zbase )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult )
.

Definition mod_inv_gmp_partial_solve_wit_23 := mod_inv_gmp_partial_solve_wit_23_pure -> mod_inv_gmp_partial_solve_wit_23_aux.

Definition mod_inv_gmp_partial_solve_wit_24_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (out_2: Z) (PreH1 : (mod_norm_spec zp_low_level_spec (zbase * zbase ) out_2 )) (PreH2 : (mod_norm_spec zp_low_level_spec (zresult * zbase ) out )) (PreH3 : (retval = 1)) (PreH4 : ((zexp % ( 2 ) ) = 1)) (PreH5 : (s > 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (result <> 0)) (PreH10 : (base <> 0)) (PreH11 : (exp <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 < za_low_level_spec)) (PreH15 : (za_low_level_spec < zp_low_level_spec)) (PreH16 : (0 <= zresult)) (PreH17 : (zresult < zp_low_level_spec)) (PreH18 : (0 <= zbase)) (PreH19 : (zbase < zp_low_level_spec)) (PreH20 : (0 <= zexp)) (PreH21 : (same_sign s zexp )) (PreH22 : (mpz_div_qr_ret_ok s zexp )) (PreH23 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH24 : (retval <> 0)) ,
  (store_Z base out_2 )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  “ (exp = exp) ” 
  &&  “ (1 >= 0) ” 
  &&  “ ((1 ÷ 32 ) <= INT_MAX) ”
.

Definition mod_inv_gmp_partial_solve_wit_24_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (out_2: Z) (PreH1 : (mod_norm_spec zp_low_level_spec (zbase * zbase ) out_2 )) (PreH2 : (mod_norm_spec zp_low_level_spec (zresult * zbase ) out )) (PreH3 : (retval = 1)) (PreH4 : ((zexp % ( 2 ) ) = 1)) (PreH5 : (s > 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (result <> 0)) (PreH10 : (base <> 0)) (PreH11 : (exp <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 < za_low_level_spec)) (PreH15 : (za_low_level_spec < zp_low_level_spec)) (PreH16 : (0 <= zresult)) (PreH17 : (zresult < zp_low_level_spec)) (PreH18 : (0 <= zbase)) (PreH19 : (zbase < zp_low_level_spec)) (PreH20 : (0 <= zexp)) (PreH21 : (same_sign s zexp )) (PreH22 : (mpz_div_qr_ret_ok s zexp )) (PreH23 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH24 : (retval <> 0)) ,
  (store_Z base out_2 )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  “ (exp = exp) ” 
  &&  “ (1 >= 0) ” 
  &&  “ ((1 ÷ 32 ) <= INT_MAX) ” 
  &&  “ (mod_norm_spec zp_low_level_spec (zbase * zbase ) out_2 ) ” 
  &&  “ (mod_norm_spec zp_low_level_spec (zresult * zbase ) out ) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((zexp % ( 2 ) ) = 1) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_Z exp zexp )
  **  (store_Z base out_2 )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_24 := mod_inv_gmp_partial_solve_wit_24_pure -> mod_inv_gmp_partial_solve_wit_24_aux.

Definition mod_inv_gmp_partial_solve_wit_25_pure := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec (zbase * zbase ) out )) (PreH2 : (retval = 0)) (PreH3 : ((zexp % ( 2 ) ) = 0)) (PreH4 : (s > 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (result <> 0)) (PreH9 : (base <> 0)) (PreH10 : (exp <> 0)) (PreH11 : (tmp <> 0)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 < za_low_level_spec)) (PreH14 : (za_low_level_spec < zp_low_level_spec)) (PreH15 : (0 <= zresult)) (PreH16 : (zresult < zp_low_level_spec)) (PreH17 : (0 <= zbase)) (PreH18 : (zbase < zp_low_level_spec)) (PreH19 : (0 <= zexp)) (PreH20 : (same_sign s zexp )) (PreH21 : (mpz_div_qr_ret_ok s zexp )) (PreH22 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH23 : (retval = 0)) ,
  (store_Z base out )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result)
  **  ((( &( "base" ) )) # Ptr  |-> base)
  **  ((( &( "exp" ) )) # Ptr  |-> exp)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "odd" ) )) # Int  |-> retval)
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult )
|--
  “ (exp = exp) ” 
  &&  “ (1 >= 0) ” 
  &&  “ ((1 ÷ 32 ) <= INT_MAX) ”
.

Definition mod_inv_gmp_partial_solve_wit_25_aux := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (PreH1 : (mod_norm_spec zp_low_level_spec (zbase * zbase ) out )) (PreH2 : (retval = 0)) (PreH3 : ((zexp % ( 2 ) ) = 0)) (PreH4 : (s > 0)) (PreH5 : (r_pre <> 0)) (PreH6 : (a_pre <> 0)) (PreH7 : (p_pre <> 0)) (PreH8 : (result <> 0)) (PreH9 : (base <> 0)) (PreH10 : (exp <> 0)) (PreH11 : (tmp <> 0)) (PreH12 : (prime zp_low_level_spec )) (PreH13 : (0 < za_low_level_spec)) (PreH14 : (za_low_level_spec < zp_low_level_spec)) (PreH15 : (0 <= zresult)) (PreH16 : (zresult < zp_low_level_spec)) (PreH17 : (0 <= zbase)) (PreH18 : (zbase < zp_low_level_spec)) (PreH19 : (0 <= zexp)) (PreH20 : (same_sign s zexp )) (PreH21 : (mpz_div_qr_ret_ok s zexp )) (PreH22 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH23 : (retval = 0)) ,
  (store_Z base out )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z exp zexp )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult )
|--
  “ (exp = exp) ” 
  &&  “ (1 >= 0) ” 
  &&  “ ((1 ÷ 32 ) <= INT_MAX) ” 
  &&  “ (mod_norm_spec zp_low_level_spec (zbase * zbase ) out ) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((zexp % ( 2 ) ) = 0) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z exp zexp )
  **  (store_Z base out )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult )
.

Definition mod_inv_gmp_partial_solve_wit_25 := mod_inv_gmp_partial_solve_wit_25_pure -> mod_inv_gmp_partial_solve_wit_25_aux.

Definition mod_inv_gmp_partial_solve_wit_26 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (out_2: Z) (PreH1 : (exp = exp)) (PreH2 : (mod_norm_spec zp_low_level_spec (zbase * zbase ) out_2 )) (PreH3 : (mod_norm_spec zp_low_level_spec (zresult * zbase ) out )) (PreH4 : (retval = 1)) (PreH5 : ((zexp % ( 2 ) ) = 1)) (PreH6 : (s > 0)) (PreH7 : (r_pre <> 0)) (PreH8 : (a_pre <> 0)) (PreH9 : (p_pre <> 0)) (PreH10 : (result <> 0)) (PreH11 : (base <> 0)) (PreH12 : (exp <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (prime zp_low_level_spec )) (PreH15 : (0 < za_low_level_spec)) (PreH16 : (za_low_level_spec < zp_low_level_spec)) (PreH17 : (0 <= zresult)) (PreH18 : (zresult < zp_low_level_spec)) (PreH19 : (0 <= zbase)) (PreH20 : (zbase < zp_low_level_spec)) (PreH21 : (0 <= zexp)) (PreH22 : (same_sign s zexp )) (PreH23 : (mpz_div_qr_ret_ok s zexp )) (PreH24 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH25 : (retval <> 0)) ,
  (store_Z exp (Z.quot (zexp) ((Z.pow (2) (1)))) )
  **  (store_Z base out_2 )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
|--
  “ (mod_norm_spec zp_low_level_spec (zbase * zbase ) out_2 ) ” 
  &&  “ (mod_norm_spec zp_low_level_spec (zresult * zbase ) out ) ” 
  &&  “ (retval = 1) ” 
  &&  “ ((zexp % ( 2 ) ) = 1) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval <> 0) ”
  &&  (store_Z exp (Z.quot (zexp) ((Z.pow (2) (1)))) )
  **  (store_Z base out_2 )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result out )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_27 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (retval: Z) (out: Z) (PreH1 : (exp = exp)) (PreH2 : (mod_norm_spec zp_low_level_spec (zbase * zbase ) out )) (PreH3 : (retval = 0)) (PreH4 : ((zexp % ( 2 ) ) = 0)) (PreH5 : (s > 0)) (PreH6 : (r_pre <> 0)) (PreH7 : (a_pre <> 0)) (PreH8 : (p_pre <> 0)) (PreH9 : (result <> 0)) (PreH10 : (base <> 0)) (PreH11 : (exp <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (prime zp_low_level_spec )) (PreH14 : (0 < za_low_level_spec)) (PreH15 : (za_low_level_spec < zp_low_level_spec)) (PreH16 : (0 <= zresult)) (PreH17 : (zresult < zp_low_level_spec)) (PreH18 : (0 <= zbase)) (PreH19 : (zbase < zp_low_level_spec)) (PreH20 : (0 <= zexp)) (PreH21 : (same_sign s zexp )) (PreH22 : (mpz_div_qr_ret_ok s zexp )) (PreH23 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) (PreH24 : (retval = 0)) ,
  (store_Z exp (Z.quot (zexp) ((Z.pow (2) (1)))) )
  **  (store_Z base out )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult )
|--
  “ (mod_norm_spec zp_low_level_spec (zbase * zbase ) out ) ” 
  &&  “ (retval = 0) ” 
  &&  “ ((zexp % ( 2 ) ) = 0) ” 
  &&  “ (s > 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ” 
  &&  “ (retval = 0) ”
  &&  (store_Z exp (Z.quot (zexp) ((Z.pow (2) (1)))) )
  **  (store_Z base out )
  **  (store_Z tmp (zbase * zbase ) )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z result zresult )
.

Definition mod_inv_gmp_partial_solve_wit_28 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (old_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  (store_Z r_pre old_low_level_spec )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
|--
  “ (s <= 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z r_pre old_low_level_spec )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
.

Definition mod_inv_gmp_partial_solve_wit_29 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (ztmp: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
  **  (store_Z tmp ztmp )
|--
  “ (s <= 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z tmp ztmp )
  **  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
.

Definition mod_inv_gmp_partial_solve_wit_30 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
|--
  “ (s <= 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((tmp)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
.

Definition mod_inv_gmp_partial_solve_wit_31 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
  **  (store_Z exp zexp )
|--
  “ (s <= 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z exp zexp )
  **  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
.

Definition mod_inv_gmp_partial_solve_wit_32 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  ((&((exp)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((exp)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((exp)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
|--
  “ (s <= 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((&((exp)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((exp)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((exp)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
.

Definition mod_inv_gmp_partial_solve_wit_33 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
  **  (store_Z base zbase )
|--
  “ (s <= 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z base zbase )
  **  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_34 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  ((&((base)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((base)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((base)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (s <= 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((&((base)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((base)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((base)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_35 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  (store_Z r_pre zresult )
  **  (store_Z result zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (s <= 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  (store_Z result zresult )
  **  (store_Z r_pre zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Definition mod_inv_gmp_partial_solve_wit_36 := 
forall (p_pre: Z) (a_pre: Z) (r_pre: Z) (zp_low_level_spec: Z) (za_low_level_spec: Z) (s: Z) (zexp: Z) (zbase: Z) (zresult: Z) (tmp: Z) (exp: Z) (base: Z) (result: Z) (ptr: Z) (cap: Z) (size: Z) (PreH1 : (s <= 0)) (PreH2 : (r_pre <> 0)) (PreH3 : (a_pre <> 0)) (PreH4 : (p_pre <> 0)) (PreH5 : (result <> 0)) (PreH6 : (base <> 0)) (PreH7 : (exp <> 0)) (PreH8 : (tmp <> 0)) (PreH9 : (prime zp_low_level_spec )) (PreH10 : (0 < za_low_level_spec)) (PreH11 : (za_low_level_spec < zp_low_level_spec)) (PreH12 : (0 <= zresult)) (PreH13 : (zresult < zp_low_level_spec)) (PreH14 : (0 <= zbase)) (PreH15 : (zbase < zp_low_level_spec)) (PreH16 : (0 <= zexp)) (PreH17 : (same_sign s zexp )) (PreH18 : (mpz_div_qr_ret_ok s zexp )) (PreH19 : (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp )) ,
  ((&((result)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((result)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((result)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z r_pre zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
|--
  “ (s <= 0) ” 
  &&  “ (r_pre <> 0) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (p_pre <> 0) ” 
  &&  “ (result <> 0) ” 
  &&  “ (base <> 0) ” 
  &&  “ (exp <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (prime zp_low_level_spec ) ” 
  &&  “ (0 < za_low_level_spec) ” 
  &&  “ (za_low_level_spec < zp_low_level_spec) ” 
  &&  “ (0 <= zresult) ” 
  &&  “ (zresult < zp_low_level_spec) ” 
  &&  “ (0 <= zbase) ” 
  &&  “ (zbase < zp_low_level_spec) ” 
  &&  “ (0 <= zexp) ” 
  &&  “ (same_sign s zexp ) ” 
  &&  “ (mpz_div_qr_ret_ok s zexp ) ” 
  &&  “ (mod_inv_pow_loop zp_low_level_spec za_low_level_spec zresult zbase zexp ) ”
  &&  ((&((result)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((result)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((result)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (store_Z r_pre zresult )
  **  (store_Z a_pre za_low_level_spec )
  **  (store_Z p_pre zp_low_level_spec )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.
Include ge_gmp_array_Strategy_Correct.
Include mpz_tdiv_r_read0_Strategy_Correct.

Axiom proof_of_mpz_odd_positive_safety_wit_1 : mpz_odd_positive_safety_wit_1.
Axiom proof_of_mpz_odd_positive_safety_wit_2 : mpz_odd_positive_safety_wit_2.
Axiom proof_of_mpz_odd_positive_safety_wit_3 : mpz_odd_positive_safety_wit_3.
Axiom proof_of_mpz_odd_positive_safety_wit_4 : mpz_odd_positive_safety_wit_4.
Axiom proof_of_mpz_odd_positive_entail_wit_1 : mpz_odd_positive_entail_wit_1.
Axiom proof_of_mpz_odd_positive_entail_wit_2 : mpz_odd_positive_entail_wit_2.
Axiom proof_of_mpz_odd_positive_return_wit_1 : mpz_odd_positive_return_wit_1.
Axiom proof_of_mpz_odd_positive_return_wit_2 : mpz_odd_positive_return_wit_2.
Axiom proof_of_mpz_odd_positive_partial_solve_wit_1 : mpz_odd_positive_partial_solve_wit_1.
Axiom proof_of_mod_inv_gmp_safety_wit_1 : mod_inv_gmp_safety_wit_1.
Axiom proof_of_mod_inv_gmp_safety_wit_2 : mod_inv_gmp_safety_wit_2.
Axiom proof_of_mod_inv_gmp_safety_wit_3 : mod_inv_gmp_safety_wit_3.
Axiom proof_of_mod_inv_gmp_safety_wit_4 : mod_inv_gmp_safety_wit_4.
Axiom proof_of_mod_inv_gmp_safety_wit_5 : mod_inv_gmp_safety_wit_5.
Axiom proof_of_mod_inv_gmp_safety_wit_6 : mod_inv_gmp_safety_wit_6.
Axiom proof_of_mod_inv_gmp_safety_wit_7 : mod_inv_gmp_safety_wit_7.
Axiom proof_of_mod_inv_gmp_safety_wit_8 : mod_inv_gmp_safety_wit_8.
Axiom proof_of_mod_inv_gmp_entail_wit_1_1 : mod_inv_gmp_entail_wit_1_1.
Axiom proof_of_mod_inv_gmp_entail_wit_1_2 : mod_inv_gmp_entail_wit_1_2.
Axiom proof_of_mod_inv_gmp_entail_wit_2_1 : mod_inv_gmp_entail_wit_2_1.
Axiom proof_of_mod_inv_gmp_entail_wit_2_2 : mod_inv_gmp_entail_wit_2_2.
Axiom proof_of_mod_inv_gmp_entail_wit_3_1 : mod_inv_gmp_entail_wit_3_1.
Axiom proof_of_mod_inv_gmp_entail_wit_3_2 : mod_inv_gmp_entail_wit_3_2.
Axiom proof_of_mod_inv_gmp_entail_wit_4_1 : mod_inv_gmp_entail_wit_4_1.
Axiom proof_of_mod_inv_gmp_entail_wit_4_2 : mod_inv_gmp_entail_wit_4_2.
Axiom proof_of_mod_inv_gmp_entail_wit_4_3 : mod_inv_gmp_entail_wit_4_3.
Axiom proof_of_mod_inv_gmp_entail_wit_4_4 : mod_inv_gmp_entail_wit_4_4.
Axiom proof_of_mod_inv_gmp_entail_wit_4_5 : mod_inv_gmp_entail_wit_4_5.
Axiom proof_of_mod_inv_gmp_entail_wit_4_6 : mod_inv_gmp_entail_wit_4_6.
Axiom proof_of_mod_inv_gmp_return_wit_1 : mod_inv_gmp_return_wit_1.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_1 : mod_inv_gmp_partial_solve_wit_1.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_2 : mod_inv_gmp_partial_solve_wit_2.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_3 : mod_inv_gmp_partial_solve_wit_3.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_4 : mod_inv_gmp_partial_solve_wit_4.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_5 : mod_inv_gmp_partial_solve_wit_5.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_6 : mod_inv_gmp_partial_solve_wit_6.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_7 : mod_inv_gmp_partial_solve_wit_7.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_8 : mod_inv_gmp_partial_solve_wit_8.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_9_pure : mod_inv_gmp_partial_solve_wit_9_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_9 : mod_inv_gmp_partial_solve_wit_9.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_10 : mod_inv_gmp_partial_solve_wit_10.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_11_pure : mod_inv_gmp_partial_solve_wit_11_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_11 : mod_inv_gmp_partial_solve_wit_11.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_12 : mod_inv_gmp_partial_solve_wit_12.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_13_pure : mod_inv_gmp_partial_solve_wit_13_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_13 : mod_inv_gmp_partial_solve_wit_13.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_14 : mod_inv_gmp_partial_solve_wit_14.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_15_pure : mod_inv_gmp_partial_solve_wit_15_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_15 : mod_inv_gmp_partial_solve_wit_15.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_16 : mod_inv_gmp_partial_solve_wit_16.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_17_pure : mod_inv_gmp_partial_solve_wit_17_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_17 : mod_inv_gmp_partial_solve_wit_17.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_18 : mod_inv_gmp_partial_solve_wit_18.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_19 : mod_inv_gmp_partial_solve_wit_19.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_20_pure : mod_inv_gmp_partial_solve_wit_20_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_20 : mod_inv_gmp_partial_solve_wit_20.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_21_pure : mod_inv_gmp_partial_solve_wit_21_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_21 : mod_inv_gmp_partial_solve_wit_21.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_22_pure : mod_inv_gmp_partial_solve_wit_22_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_22 : mod_inv_gmp_partial_solve_wit_22.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_23_pure : mod_inv_gmp_partial_solve_wit_23_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_23 : mod_inv_gmp_partial_solve_wit_23.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_24_pure : mod_inv_gmp_partial_solve_wit_24_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_24 : mod_inv_gmp_partial_solve_wit_24.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_25_pure : mod_inv_gmp_partial_solve_wit_25_pure.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_25 : mod_inv_gmp_partial_solve_wit_25.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_26 : mod_inv_gmp_partial_solve_wit_26.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_27 : mod_inv_gmp_partial_solve_wit_27.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_28 : mod_inv_gmp_partial_solve_wit_28.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_29 : mod_inv_gmp_partial_solve_wit_29.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_30 : mod_inv_gmp_partial_solve_wit_30.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_31 : mod_inv_gmp_partial_solve_wit_31.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_32 : mod_inv_gmp_partial_solve_wit_32.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_33 : mod_inv_gmp_partial_solve_wit_33.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_34 : mod_inv_gmp_partial_solve_wit_34.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_35 : mod_inv_gmp_partial_solve_wit_35.
Axiom proof_of_mod_inv_gmp_partial_solve_wit_36 : mod_inv_gmp_partial_solve_wit_36.

End VC_Correct.
