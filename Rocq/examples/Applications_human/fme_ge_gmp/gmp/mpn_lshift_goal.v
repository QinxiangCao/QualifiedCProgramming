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
Local Open Scope sac.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_strategy_proof.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import gmp_optional_strategy_proof.

(*----- Function mpn_lshift -----*)

Definition mpn_lshift_safety_wit_1_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_lshift_safety_wit_2_nonalias := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_lshift_safety_wit_3_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_lshift_safety_wit_4_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_5_nonalias := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_lshift_safety_wit_6_nonalias := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_7_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_inplace 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((32 - cnt_pre ) <= 31) ” 
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_lshift_safety_wit_8_nonalias := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_nonalias 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((32 - cnt_pre ) <= 31) ” 
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_lshift_safety_wit_9_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_inplace 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_10_nonalias := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_nonalias 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_11_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) (PreH17 : (tnc = (32 - cnt_pre ))) (PreH18 : (1 <= cnt_pre)) (PreH19 : (cnt_pre < 32)) (PreH20 : (0 <= low_limb)) (PreH21 : (low_limb <= UINT_MAX)) (PreH22 : (i = (n_pre - 1 ))) (PreH23 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH24 : (0 <= i)) (PreH25 : (i < n_pre)) (PreH26 : ((Zlength (l_up_inplace)) = n_pre)) (PreH27 : (l_done = (@nil Z))) (PreH28 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH29 : (list_within_bound UINT_MOD l_up_inplace )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH34 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_12_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) (PreH17 : (tnc = (32 - cnt_pre ))) (PreH18 : (1 <= cnt_pre)) (PreH19 : (cnt_pre < 32)) (PreH20 : (0 <= low_limb)) (PreH21 : (low_limb <= UINT_MAX)) (PreH22 : (i = (n_pre - 1 ))) (PreH23 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH24 : (0 <= i)) (PreH25 : (i < n_pre)) (PreH26 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH27 : (l_done = (@nil Z))) (PreH28 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH29 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH34 : (rp_pre <> up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_13_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i_2: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_2 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_lshift_safety_wit_14_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_15_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i_2: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_lshift_safety_wit_16_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_17_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_lshift_safety_wit_18_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_lshift_safety_wit_19_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_20_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_21_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (tnc <= 31) ” 
  &&  “ (0 <= tnc) ”
.

Definition mpn_lshift_safety_wit_22_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (tnc <= 31) ” 
  &&  “ (0 <= tnc) ”
.

Definition mpn_lshift_safety_wit_23_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (replace_Znth (((i + 1 ) - (i + 1 ) )) ((Z.lor high_limb (Z.shiftr low_limb tnc))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_24_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) ,
  (((rp_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb (Z.shiftr low_limb tnc)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_25_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (0 = 0)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_26_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (0 = 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (i = 0)) (PreH8 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH13 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH14 : (rp_pre <> up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_entail_wit_1_nonalias := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (rp_pre <> up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_entail_wit_2_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (rp_pre = up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  (UIntArray.full up_pre n_pre l_up_inplace )
.

Definition mpn_lshift_entail_wit_3_nonalias := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.undef_seg rp_pre 0 n_pre )
  **  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_done: (@list Z)) ,
  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth (n_pre - 1 ) l_up_nonalias 0)) ” 
  &&  “ ((Znth (n_pre - 1 ) l_up_nonalias 0) <= UINT_MAX) ” 
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ” 
  &&  “ ((Znth (n_pre - 1 ) l_up_nonalias 0) = (Znth ((n_pre - 1 )) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 ((n_pre - 1 ) + 1 ) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ ((Znth (n_pre - 1 ) l_up_nonalias 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (n_pre - 1 ) l_up_nonalias 0)) ”
  &&  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
).

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_5 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_6 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ ((Znth (n_pre - 1 ) l_up_nonalias 0) <= UINT_MAX) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_7 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  “ (0 <= (Znth (n_pre - 1 ) l_up_nonalias 0)) ”
.

Definition mpn_lshift_entail_wit_3_nonalias_split_goal_spatial := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH4 : (rp_pre <> up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
|--
  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
.

Definition mpn_lshift_entail_wit_4_inplace := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  EX (l_done: (@list Z)) ,
  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth (n_pre - 1 ) l_up_inplace 0)) ” 
  &&  “ ((Znth (n_pre - 1 ) l_up_inplace 0) <= UINT_MAX) ” 
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ” 
  &&  “ ((Znth (n_pre - 1 ) l_up_inplace 0) = (Znth ((n_pre - 1 )) (l_up_inplace) (0))) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ ((Znth (n_pre - 1 ) l_up_inplace 0) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth (n_pre - 1 ) l_up_inplace 0)) ” 
  &&  “ ((sublist (0) (n_pre) (l_up_inplace)) = (app ((sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace))) ((@nil Z)))) ” 
  &&  “ ((Zlength ((sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace)))) = (((n_pre - 1 ) + 1 ) - 0 )) ”
  &&  emp
).

Definition mpn_lshift_entail_wit_4_inplace_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_5 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_6 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((Znth (n_pre - 1 ) l_up_inplace 0) <= UINT_MAX) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_7 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ (0 <= (Znth (n_pre - 1 ) l_up_inplace 0)) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_8 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((sublist (0) (n_pre) (l_up_inplace)) = (app ((sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace))) ((@nil Z)))) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_9 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  “ ((Zlength ((sublist (0) (((n_pre - 1 ) + 1 )) (l_up_inplace)))) = (((n_pre - 1 ) + 1 ) - 0 )) ”
.

Definition mpn_lshift_entail_wit_4_inplace_split_goal_spatial := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
|--
  TT && emp 
.

Definition mpn_lshift_entail_wit_5_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = (n_pre - 1 ))) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : (l_done = (@nil Z))) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_inplace )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done )
|--
  EX (l_done_2: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_entail_wit_6_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = (n_pre - 1 ))) (PreH7 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : (l_done = (@nil Z))) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (rp_pre <> up_pre)) ,
  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_done_2: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_entail_wit_7_nonalias_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb_2: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)) ,
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth (i - 1 ) l_up_nonalias 0)) ” 
  &&  “ ((Znth (i - 1 ) l_up_nonalias 0) <= UINT_MAX) ” 
  &&  “ ((Znth (i - 1 ) l_up_nonalias 0) = (Znth ((i - 1 )) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 ((i - 1 ) + 2 ) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb_2: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)) ,
  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth (i - 1 ) l_up_nonalias 0)) ” 
  &&  “ ((Znth (i - 1 ) l_up_nonalias 0) <= UINT_MAX) ” 
  &&  “ ((Znth (i - 1 ) l_up_nonalias 0) = (Znth ((i - 1 )) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
).

Definition mpn_lshift_entail_wit_8_inplace_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb_2: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0)) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0) <= UINT_MAX) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0) = (Znth ((i - 1 )) (l_up_inplace) (0))) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre ((i - 1 ) + 2 ) n_pre l_done )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb_2: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0)) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0) <= UINT_MAX) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_inplace)) 0) = (Znth ((i - 1 )) (l_up_inplace) (0))) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre ((i - 1 ) + 2 ) n_pre l_done )
).

Definition mpn_lshift_entail_wit_9_inplace_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre (i_2 + 1 ) (i_2 + 2 ) (replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z))  (high_limb: Z)  (retval: Z)  (l_done: (@list Z))  (i: Z)  (low_limb: Z)  (tnc: Z) ,
  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb_2) ” 
  &&  “ (low_limb_2 <= UINT_MAX) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_inplace) (0))) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  TT && emp 
|--
  “ ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (Znth ((n_pre - 1 )) (l_up_inplace) (0))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)))) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits ((low_limb_2 * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (list_within_bound UINT_MOD (app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)) ) ” 
  &&  “ ((Zlength ((app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)))) = (n_pre - (i_2 + 1 ) )) ”
  &&  emp
).

Definition mpn_lshift_entail_wit_9_inplace_inv_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))
.

Definition mpn_lshift_entail_wit_9_inplace_inv_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  (list_within_bound UINT_MOD (@nil Z) )
.

Definition mpn_lshift_entail_wit_9_inplace_inv_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) ))
.

Definition mpn_lshift_entail_wit_9_inplace_inv_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) <= UINT_MAX)
.

Definition mpn_lshift_entail_wit_9_inplace_inv_split_goal_5 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  (0 <= (Znth ((n_pre - 1 )) (l_up_inplace) (0)))
.

Definition mpn_lshift_entail_wit_9_inplace_inv_split_goal_6 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)))) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))
.

Definition mpn_lshift_entail_wit_9_inplace_inv_split_goal_7 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits ((low_limb_2 * (Z.pow (2) (cnt_pre)) )) (32)))
.

Definition mpn_lshift_entail_wit_9_inplace_inv_split_goal_8 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  (list_within_bound UINT_MOD (app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)) )
.

Definition mpn_lshift_entail_wit_9_inplace_inv_split_goal_9 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((Zlength ((app ((replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 (32 - cnt_pre )))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_inplace))))) (l_done_3)))) = (n_pre - (i_2 + 1 ) ))
.

Definition mpn_lshift_entail_wit_10_nonalias_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (tnc_2 = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb_2)) (PreH5 : (low_limb_2 <= UINT_MAX)) (PreH6 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH7 : (0 <= i_2)) (PreH8 : ((i_2 + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) ,
  (((rp_pre + ((i_2 + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)))
  **  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_done_2: (@list Z))  (high_limb: Z)  (retval: Z)  (l_done: (@list Z))  (i: Z)  (low_limb: Z)  (tnc: Z) ,
  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb_2) ” 
  &&  “ (low_limb_2 <= UINT_MAX) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) <= UINT_MAX)) (PreH2 : ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) >= 0)) (PreH3 : (tnc_2 = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb_2)) (PreH7 : (low_limb_2 <= UINT_MAX)) (PreH8 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH9 : (0 <= i_2)) (PreH10 : ((i_2 + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH12 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH14 : (list_within_bound UINT_MOD l_done_3 )) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (rp_pre <> up_pre)) ,
  (((rp_pre + ((i_2 + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)))
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z)) ,
  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb_2) ” 
  &&  “ (low_limb_2 <= UINT_MAX) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth ((n_pre - 1 )) (l_up_nonalias) (0))) ” 
  &&  “ ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) <= UINT_MAX) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
).

Definition mpn_lshift_entail_wit_11_nonalias_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb_2)) (PreH22 : (low_limb_2 <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)) ,
  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb_2)) (PreH22 : (low_limb_2 <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)) ,
  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.seg rp_pre 1 n_pre l_done )
).

Definition mpn_lshift_entail_wit_12_inplace_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb_2)) (PreH22 : (low_limb_2 <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (l_done_3: (@list Z)) (i: Z) (low_limb: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc_2 = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb_2)) (PreH22 : (low_limb_2 <= UINT_MAX)) (PreH23 : (i_2 = (n_pre - 1 ))) (PreH24 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH33 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
).

Definition mpn_lshift_return_wit_1_inplace_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre = up_pre)) ,
  (UIntArray.full up_pre 1 (replace_Znth (0) (high_limb) ((sublist (0) (1) (l_up_inplace)))) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre = up_pre)) ,
  (UIntArray.full up_pre 1 (replace_Znth (0) (high_limb) ((sublist (0) (1) (l_up_inplace)))) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
).

Definition mpn_lshift_return_wit_2_nonalias_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre <> up_pre)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (high_limb <= UINT_MAX)) (PreH2 : (high_limb >= 0)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH15 : (rp_pre <> up_pre)) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
).

Definition mpn_lshift_partial_solve_wit_1_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (rp_pre = up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  (((up_pre + ((n_pre - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (n_pre - 1 ) l_up_inplace 0))
  **  (UIntArray.missing_i up_pre (n_pre - 1 ) 0 n_pre l_up_inplace )
.

Definition mpn_lshift_partial_solve_wit_2_nonalias := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (rp_pre <> up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  (((up_pre + ((n_pre - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (n_pre - 1 ) l_up_nonalias 0))
  **  (UIntArray.missing_i up_pre (n_pre - 1 ) 0 n_pre l_up_nonalias )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_lshift_partial_solve_wit_3_nonalias_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth (n_pre - 1 ) l_up_nonalias 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_nonalias 0))
  **  ((( &( "high_limb" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_nonalias 0) cnt_pre)) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (rp_pre <> up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_3_nonalias_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_nonalias )) ,
  (UIntArray.full up_pre n_pre l_up_nonalias )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (rp_pre <> up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ (rp_pre <> up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ”
  &&  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_partial_solve_wit_3_nonalias := mpn_lshift_partial_solve_wit_3_nonalias_pure -> mpn_lshift_partial_solve_wit_3_nonalias_aux.

Definition mpn_lshift_partial_solve_wit_4_inplace_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth (n_pre - 1 ) l_up_inplace 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth (n_pre - 1 ) l_up_inplace 0))
  **  ((( &( "high_limb" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth (n_pre - 1 ) l_up_inplace 0) cnt_pre)) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (rp_pre = up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_4_inplace_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (rp_pre = up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  (UIntArray.full up_pre n_pre l_up_inplace )
.

Definition mpn_lshift_partial_solve_wit_4_inplace := mpn_lshift_partial_solve_wit_4_inplace_pure -> mpn_lshift_partial_solve_wit_4_inplace_aux.

Definition mpn_lshift_partial_solve_wit_5_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i_2) (l_up_inplace) (0)))) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_inplace)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_inplace )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (i_2 > 0) ” 
  &&  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb_2) ” 
  &&  “ (low_limb_2 <= UINT_MAX) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_inplace) (0))) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (((up_pre + ((i_2 - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((i_2 - 1 ) - 0 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) 0))
  **  (UIntArray.missing_i up_pre (i_2 - 1 ) 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i_2 + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_partial_solve_wit_6_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (l_done_2: (@list Z)) (i_2: Z) (low_limb_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (tnc_2 = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb_2)) (PreH6 : (low_limb_2 <= UINT_MAX)) (PreH7 : (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0)))) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre <> up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (0 <= low_limb)) (PreH22 : (low_limb <= UINT_MAX)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH35 : (rp_pre <> up_pre)) ,
  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (i_2 > 0) ” 
  &&  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb_2) ” 
  &&  “ (low_limb_2 <= UINT_MAX) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (((up_pre + ((i_2 - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth (i_2 - 1 ) l_up_nonalias 0))
  **  (UIntArray.missing_i up_pre (i_2 - 1 ) 0 n_pre l_up_nonalias )
  **  (UIntArray.undef_seg rp_pre 0 (i_2 + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_partial_solve_wit_7_nonalias_inv_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.undef_seg rp_pre 0 (i + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((i + 1 ) >= 0) ” 
  &&  “ ((i + 2 ) <= n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_7_nonalias_inv_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) ,
  (UIntArray.undef_seg rp_pre 0 (i + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ ((i + 1 ) >= 0) ” 
  &&  “ ((i + 2 ) <= n_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 (i + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_partial_solve_wit_7_nonalias_inv := mpn_lshift_partial_solve_wit_7_nonalias_inv_pure -> mpn_lshift_partial_solve_wit_7_nonalias_inv_aux.

Definition mpn_lshift_partial_solve_wit_8_inplace_inv_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (up_pre = up_pre) ” 
  &&  “ ((i + 1 ) >= 0) ” 
  &&  “ ((i + 2 ) <= n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_8_inplace_inv_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (up_pre = up_pre) ” 
  &&  “ ((i + 1 ) >= 0) ” 
  &&  “ ((i + 2 ) <= n_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_8_inplace_inv := mpn_lshift_partial_solve_wit_8_inplace_inv_pure -> mpn_lshift_partial_solve_wit_8_inplace_inv_aux.

Definition mpn_lshift_partial_solve_wit_9_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (low_limb = (Znth (i) (l_up_inplace) (0)))) (PreH8 : (0 <= i)) (PreH9 : ((i + 1 ) < n_pre)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_inplace )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
|--
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_inplace) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (((up_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre (i + 1 ) (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_10_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (low_limb = (Znth (i) (l_up_nonalias) (0)))) (PreH7 : (0 <= i)) (PreH8 : ((i + 1 ) < n_pre)) (PreH9 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (rp_pre <> up_pre)) ,
  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_nonalias) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_nonalias) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_nonalias)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (((rp_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_partial_solve_wit_11_nonalias_inv_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre <> up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (0 = 0) ”
.

Definition mpn_lshift_partial_solve_wit_11_nonalias_inv_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre <> up_pre)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (0 = 0) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_partial_solve_wit_11_nonalias_inv := mpn_lshift_partial_solve_wit_11_nonalias_inv_pure -> mpn_lshift_partial_solve_wit_11_nonalias_inv_aux.

Definition mpn_lshift_partial_solve_wit_12_inplace_inv_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 = 0) ”
.

Definition mpn_lshift_partial_solve_wit_12_inplace_inv_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= low_limb)) (PreH5 : (low_limb <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH12 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH13 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_12_inplace_inv := mpn_lshift_partial_solve_wit_12_inplace_inv_pure -> mpn_lshift_partial_solve_wit_12_inplace_inv_aux.

Definition mpn_lshift_partial_solve_wit_13_inplace_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (0 = 0)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) ))) (PreH15 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
|--
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_inplace)) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (((up_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre 0 0 1 (sublist (0) (1) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_14_nonalias_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (0 = 0)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= low_limb)) (PreH6 : (low_limb <= UINT_MAX)) (PreH7 : (i = 0)) (PreH8 : ((Zlength (l_up_nonalias)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_nonalias )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH13 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) ))) (PreH14 : (rp_pre <> up_pre)) ,
  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_nonalias ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_nonalias) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_nonalias)) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (rp_pre <> up_pre) ”
  &&  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_which_implies_wit_1 := 
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_nonalias: (@list Z)) (PreH1 : (rp_pre <> up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_nonalias)) = n_pre)) ,
  (UIntArray.undef_full rp_pre n_pre )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
|--
  “ (rp_pre <> up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_up_nonalias)) = n_pre) ”
  &&  (UIntArray.undef_seg rp_pre 0 n_pre )
  **  (UIntArray.seg rp_pre n_pre n_pre (@nil Z) )
  **  (UIntArray.full up_pre n_pre l_up_nonalias )
.

Definition mpn_lshift_which_implies_wit_2 := 
(
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (rp_pre = up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre n_pre n_pre (@nil Z) )
) \/
(
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
).

Definition mpn_lshift_which_implies_wit_2_split_goal_spatial := 
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : ((Zlength (l_up_inplace)) = n_pre)) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
.

Definition mpn_lshift_which_implies_wit_3 := 
forall (n_pre: Z) (rp_pre: Z) (i: Z) (PreH1 : ((i + 1 ) >= 0)) (PreH2 : ((i + 2 ) <= n_pre)) ,
  (UIntArray.undef_seg rp_pre 0 (i + 2 ) )
|--
  (UIntArray.undef_seg rp_pre 0 (i + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
.

Definition mpn_lshift_which_implies_wit_4 := 
(
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : ((i + 1 ) >= 0)) (PreH3 : ((i + 2 ) <= n_pre)) ,
  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_inplace)) )
|--
  “ (rp = up_pre) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)) )
) \/
(
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : ((i + 1 ) >= 0)) (PreH3 : ((i + 2 ) <= n_pre)) ,
  TT && emp 
|--
  “ ((sublist (0) ((i + 2 )) (l_up_inplace)) = (app ((sublist (0) ((i + 1 )) (l_up_inplace))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_inplace))))) ” 
  &&  “ ((Zlength ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((i + 1 ) - 0 )) ”
  &&  emp
).

Definition mpn_lshift_which_implies_wit_4_split_goal_1 := 
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : ((i + 1 ) >= 0)) (PreH3 : ((i + 2 ) <= n_pre)) ,
  ((sublist (0) ((i + 2 )) (l_up_inplace)) = (app ((sublist (0) ((i + 1 )) (l_up_inplace))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_inplace)))))
.

Definition mpn_lshift_which_implies_wit_4_split_goal_2 := 
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : ((i + 1 ) >= 0)) (PreH3 : ((i + 2 ) <= n_pre)) ,
  ((Zlength ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((i + 1 ) - 0 ))
.

Definition mpn_lshift_which_implies_wit_5 := 
forall (rp_pre: Z) (i: Z) (PreH1 : (i = 0)) ,
  (UIntArray.undef_seg rp_pre 0 1 )
|--
  “ (i = 0) ”
  &&  (UIntArray.undef_seg rp_pre 0 1 )
.

Definition mpn_lshift_which_implies_wit_6 := 
forall (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (i = 0)) ,
  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_inplace)) )
|--
  “ (rp = up_pre) ” 
  &&  “ (i = 0) ”
  &&  (UIntArray.seg rp 0 1 (sublist (0) (1) (l_up_inplace)) )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_lshift_safety_wit_1_inplace : mpn_lshift_safety_wit_1_inplace.
Axiom proof_of_mpn_lshift_safety_wit_2_nonalias : mpn_lshift_safety_wit_2_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_3_inplace : mpn_lshift_safety_wit_3_inplace.
Axiom proof_of_mpn_lshift_safety_wit_4_inplace : mpn_lshift_safety_wit_4_inplace.
Axiom proof_of_mpn_lshift_safety_wit_5_nonalias : mpn_lshift_safety_wit_5_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_6_nonalias : mpn_lshift_safety_wit_6_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_7_inplace : mpn_lshift_safety_wit_7_inplace.
Axiom proof_of_mpn_lshift_safety_wit_8_nonalias : mpn_lshift_safety_wit_8_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_9_inplace : mpn_lshift_safety_wit_9_inplace.
Axiom proof_of_mpn_lshift_safety_wit_10_nonalias : mpn_lshift_safety_wit_10_nonalias.
Axiom proof_of_mpn_lshift_safety_wit_11_inplace_inv : mpn_lshift_safety_wit_11_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_12_nonalias_inv : mpn_lshift_safety_wit_12_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_13_inplace_inv : mpn_lshift_safety_wit_13_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_14_inplace_inv : mpn_lshift_safety_wit_14_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_15_nonalias_inv : mpn_lshift_safety_wit_15_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_16_nonalias_inv : mpn_lshift_safety_wit_16_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_17_nonalias_inv : mpn_lshift_safety_wit_17_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_18_inplace_inv : mpn_lshift_safety_wit_18_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_19_inplace_inv : mpn_lshift_safety_wit_19_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_20_nonalias_inv : mpn_lshift_safety_wit_20_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_21_inplace_inv : mpn_lshift_safety_wit_21_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_22_nonalias_inv : mpn_lshift_safety_wit_22_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_23_inplace_inv : mpn_lshift_safety_wit_23_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_24_nonalias_inv : mpn_lshift_safety_wit_24_nonalias_inv.
Axiom proof_of_mpn_lshift_safety_wit_25_inplace_inv : mpn_lshift_safety_wit_25_inplace_inv.
Axiom proof_of_mpn_lshift_safety_wit_26_nonalias_inv : mpn_lshift_safety_wit_26_nonalias_inv.
Axiom proof_of_mpn_lshift_entail_wit_1_nonalias : mpn_lshift_entail_wit_1_nonalias.
Axiom proof_of_mpn_lshift_entail_wit_2_inplace : mpn_lshift_entail_wit_2_inplace.
Axiom proof_of_mpn_lshift_entail_wit_3_nonalias : mpn_lshift_entail_wit_3_nonalias.
Axiom proof_of_mpn_lshift_entail_wit_4_inplace : mpn_lshift_entail_wit_4_inplace.
Axiom proof_of_mpn_lshift_entail_wit_5_inplace_inv : mpn_lshift_entail_wit_5_inplace_inv.
Axiom proof_of_mpn_lshift_entail_wit_6_nonalias_inv : mpn_lshift_entail_wit_6_nonalias_inv.
Axiom proof_of_mpn_lshift_entail_wit_7_nonalias_inv : mpn_lshift_entail_wit_7_nonalias_inv.
Axiom proof_of_mpn_lshift_entail_wit_8_inplace_inv : mpn_lshift_entail_wit_8_inplace_inv.
Axiom proof_of_mpn_lshift_entail_wit_9_inplace_inv : mpn_lshift_entail_wit_9_inplace_inv.
Axiom proof_of_mpn_lshift_entail_wit_10_nonalias_inv : mpn_lshift_entail_wit_10_nonalias_inv.
Axiom proof_of_mpn_lshift_entail_wit_11_nonalias_inv : mpn_lshift_entail_wit_11_nonalias_inv.
Axiom proof_of_mpn_lshift_entail_wit_12_inplace_inv : mpn_lshift_entail_wit_12_inplace_inv.
Axiom proof_of_mpn_lshift_return_wit_1_inplace_inv : mpn_lshift_return_wit_1_inplace_inv.
Axiom proof_of_mpn_lshift_return_wit_2_nonalias_inv : mpn_lshift_return_wit_2_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_1_inplace : mpn_lshift_partial_solve_wit_1_inplace.
Axiom proof_of_mpn_lshift_partial_solve_wit_2_nonalias : mpn_lshift_partial_solve_wit_2_nonalias.
Axiom proof_of_mpn_lshift_partial_solve_wit_3_nonalias_pure : mpn_lshift_partial_solve_wit_3_nonalias_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_3_nonalias : mpn_lshift_partial_solve_wit_3_nonalias.
Axiom proof_of_mpn_lshift_partial_solve_wit_4_inplace_pure : mpn_lshift_partial_solve_wit_4_inplace_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_4_inplace : mpn_lshift_partial_solve_wit_4_inplace.
Axiom proof_of_mpn_lshift_partial_solve_wit_5_inplace_inv : mpn_lshift_partial_solve_wit_5_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_6_nonalias_inv : mpn_lshift_partial_solve_wit_6_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_7_nonalias_inv_pure : mpn_lshift_partial_solve_wit_7_nonalias_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_7_nonalias_inv : mpn_lshift_partial_solve_wit_7_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_8_inplace_inv_pure : mpn_lshift_partial_solve_wit_8_inplace_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_8_inplace_inv : mpn_lshift_partial_solve_wit_8_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_9_inplace_inv : mpn_lshift_partial_solve_wit_9_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_10_nonalias_inv : mpn_lshift_partial_solve_wit_10_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_11_nonalias_inv_pure : mpn_lshift_partial_solve_wit_11_nonalias_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_11_nonalias_inv : mpn_lshift_partial_solve_wit_11_nonalias_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_12_inplace_inv_pure : mpn_lshift_partial_solve_wit_12_inplace_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_12_inplace_inv : mpn_lshift_partial_solve_wit_12_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_13_inplace_inv : mpn_lshift_partial_solve_wit_13_inplace_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_14_nonalias_inv : mpn_lshift_partial_solve_wit_14_nonalias_inv.
Axiom proof_of_mpn_lshift_which_implies_wit_1 : mpn_lshift_which_implies_wit_1.
Axiom proof_of_mpn_lshift_which_implies_wit_2 : mpn_lshift_which_implies_wit_2.
Axiom proof_of_mpn_lshift_which_implies_wit_3 : mpn_lshift_which_implies_wit_3.
Axiom proof_of_mpn_lshift_which_implies_wit_4 : mpn_lshift_which_implies_wit_4.
Axiom proof_of_mpn_lshift_which_implies_wit_5 : mpn_lshift_which_implies_wit_5.
Axiom proof_of_mpn_lshift_which_implies_wit_6 : mpn_lshift_which_implies_wit_6.

End VC_Correct.
