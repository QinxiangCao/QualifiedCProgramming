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

(*----- Function mpn_rshift -----*)

Definition mpn_rshift_safety_wit_1_inplace := 
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

Definition mpn_rshift_safety_wit_2_inplace := 
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
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_safety_wit_3_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth 0 l_up_inplace 0))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((32 - cnt_pre ) <= 31) ” 
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_rshift_safety_wit_4_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "retval" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth 0 l_up_inplace 0) (32 - cnt_pre ))) (32)))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth 0 l_up_inplace 0))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_rshift_safety_wit_5_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : ((Zlength (l_done)) = i)) (PreH8 : (list_within_bound UINT_MOD l_up_inplace )) (PreH9 : (list_within_bound UINT_MOD l_done )) (PreH10 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH11 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH12 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH13 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH14 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_rshift_safety_wit_6_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : ((Zlength (l_done)) = i)) (PreH8 : (list_within_bound UINT_MOD l_up_inplace )) (PreH9 : (list_within_bound UINT_MOD l_done )) (PreH10 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH11 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH12 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH13 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH14 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_rshift_safety_wit_7_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = i)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_rshift_safety_wit_8_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = i)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_rshift_safety_wit_9_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (i - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH13 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH14 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH15 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre (i - 1 ) i (sublist ((i - 1 )) (i) (l_up_inplace)) )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_rshift_safety_wit_10_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (i - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH13 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH14 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH15 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre (i - 1 ) i (sublist ((i - 1 )) (i) (l_up_inplace)) )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_rshift_safety_wit_11_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (i - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH13 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH14 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH15 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH16 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre (i - 1 ) i (sublist ((i - 1 )) (i) (l_up_inplace)) )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done )
|--
  “ (tnc <= 31) ” 
  &&  “ (0 <= tnc) ”
.

Definition mpn_rshift_safety_wit_12_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : ((Zlength (l_up_inplace)) = n_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (i - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre (i - 1 ) i (replace_Znth (((i - 1 ) - (i - 1 ) )) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl high_limb tnc)) (32)))) ((sublist ((i - 1 )) (i) (l_up_inplace)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done )
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_rshift_entail_wit_1_inplace := 
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

Definition mpn_rshift_entail_wit_2_inplace := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (up_pre = up_pre)) (PreH2 : (0 = 0)) (PreH3 : (n_pre > 0)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) (PreH5 : (rp_pre = up_pre)) (PreH6 : (n_pre > 0)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : ((Zlength (l_up_inplace)) = n_pre)) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 0 (@nil Z) )
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
|--
  EX (l_done: (@list Z)) ,
  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = 0) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Znth 0 l_up_inplace 0) = (Znth (0) (l_up_inplace) (0))) ” 
  &&  “ ((Z.shiftr (Znth 0 l_up_inplace 0) cnt_pre) = ((Znth (0) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth 0 l_up_inplace 0) (32 - cnt_pre ))) (32)) = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + ((Z.shiftr (Znth 0 l_up_inplace 0) cnt_pre) * (Z.pow (UINT_MOD) (0)) ) ) * (Z.pow (2) (cnt_pre)) ) + ((unsigned_last_nbits ((Z.shiftl (Znth 0 l_up_inplace 0) (32 - cnt_pre ))) (32)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 0 l_done )
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (n_pre > 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) ,
  TT && emp 
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) ((@nil Z))) + ((Z.shiftr (Znth 0 l_up_inplace 0) cnt_pre) * (Z.pow (UINT_MOD) (0)) ) ) * (Z.pow (2) (cnt_pre)) ) + ((unsigned_last_nbits ((Z.shiftl (Znth 0 l_up_inplace 0) (32 - cnt_pre ))) (32)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth 0 l_up_inplace 0) (32 - cnt_pre ))) (32)) = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ” 
  &&  “ ((Z.shiftr (Znth 0 l_up_inplace 0) cnt_pre) = ((Znth (0) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition mpn_rshift_entail_wit_2_inplace_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (n_pre > 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) ,
  ((list_to_Z (UINT_MOD) ((sublist (0) ((0 + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) ((@nil Z))) + ((Z.shiftr (Znth 0 l_up_inplace 0) cnt_pre) * (Z.pow (UINT_MOD) (0)) ) ) * (Z.pow (2) (cnt_pre)) ) + ((unsigned_last_nbits ((Z.shiftl (Znth 0 l_up_inplace 0) (32 - cnt_pre ))) (32)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) ))
.

Definition mpn_rshift_entail_wit_2_inplace_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (n_pre > 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) ,
  ((unsigned_last_nbits ((Z.shiftl (Znth 0 l_up_inplace 0) (32 - cnt_pre ))) (32)) = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32)))
.

Definition mpn_rshift_entail_wit_2_inplace_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (n_pre > 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) ,
  ((Z.shiftr (Znth 0 l_up_inplace 0) cnt_pre) = ((Znth (0) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))
.

Definition mpn_rshift_entail_wit_2_inplace_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (n_pre > 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (list_within_bound UINT_MOD (@nil Z) )
.

Definition mpn_rshift_entail_wit_2_inplace_split_goal_5 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (n_pre > 0)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition mpn_rshift_entail_wit_3_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (i = 0)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : (l_done_2 = (@nil Z))) (PreH9 : ((Zlength (l_done_2)) = i)) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) (PreH11 : (list_within_bound UINT_MOD l_done_2 )) (PreH12 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH13 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH14 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH15 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH16 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 i l_done_2 )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
.

Definition mpn_rshift_entail_wit_4_inplace := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 i l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = ((i + 1 ) - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Znth ((i + 1 ) - i ) (sublist (i) (n_pre) (l_up_inplace)) 0) = (Znth ((i + 1 )) (l_up_inplace) (0))) ” 
  &&  “ (low_limb = ((Znth (((i + 1 ) - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (((i + 1 ) - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 ((i + 1 ) - 1 ) l_done )
  **  (UIntArray.seg up_pre ((i + 1 ) - 1 ) n_pre (sublist (((i + 1 ) - 1 )) (n_pre) (l_up_inplace)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 i l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = ((i + 1 ) - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Znth ((i + 1 ) - i ) (sublist (i) (n_pre) (l_up_inplace)) 0) = (Znth ((i + 1 )) (l_up_inplace) (0))) ” 
  &&  “ (low_limb = ((Znth (((i + 1 ) - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (((i + 1 ) - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 ((i + 1 ) - 1 ) l_done )
  **  (UIntArray.seg up_pre ((i + 1 ) - 1 ) n_pre (sublist (((i + 1 ) - 1 )) (n_pre) (l_up_inplace)) )
).

Definition mpn_rshift_entail_wit_5_inplace := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : ((Zlength (l_up_inplace)) = n_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = (i - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre (i - 1 ) i (replace_Znth (((i - 1 ) - (i - 1 ) )) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl high_limb tnc)) (32)))) ((sublist ((i - 1 )) (i) (l_up_inplace)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ ((Z.shiftr high_limb cnt_pre) = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + ((Z.shiftr high_limb cnt_pre) * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : ((Zlength (l_up_inplace)) = n_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = (i - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  TT && emp 
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) ((app (l_done_2) ((replace_Znth (((i - 1 ) - (i - 1 ) )) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl high_limb tnc)) (32)))) ((sublist ((i - 1 )) (i) (l_up_inplace)))))))) + ((Z.shiftr high_limb cnt_pre) * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ ((Z.shiftr high_limb cnt_pre) = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (list_within_bound UINT_MOD (app (l_done_2) ((replace_Znth (((i - 1 ) - (i - 1 ) )) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl high_limb tnc)) (32)))) ((sublist ((i - 1 )) (i) (l_up_inplace)))))) ) ” 
  &&  “ ((Zlength ((app (l_done_2) ((replace_Znth (((i - 1 ) - (i - 1 ) )) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl high_limb tnc)) (32)))) ((sublist ((i - 1 )) (i) (l_up_inplace)))))))) = i) ”
  &&  emp
).

Definition mpn_rshift_entail_wit_5_inplace_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : ((Zlength (l_up_inplace)) = n_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = (i - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) ((app (l_done_2) ((replace_Znth (((i - 1 ) - (i - 1 ) )) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl high_limb tnc)) (32)))) ((sublist ((i - 1 )) (i) (l_up_inplace)))))))) + ((Z.shiftr high_limb cnt_pre) * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))
.

Definition mpn_rshift_entail_wit_5_inplace_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : ((Zlength (l_up_inplace)) = n_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = (i - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((Z.shiftr high_limb cnt_pre) = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))
.

Definition mpn_rshift_entail_wit_5_inplace_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : ((Zlength (l_up_inplace)) = n_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = (i - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  (list_within_bound UINT_MOD (app (l_done_2) ((replace_Znth (((i - 1 ) - (i - 1 ) )) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl high_limb tnc)) (32)))) ((sublist ((i - 1 )) (i) (l_up_inplace)))))) )
.

Definition mpn_rshift_entail_wit_5_inplace_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done_2: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : ((Zlength (l_up_inplace)) = n_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (1 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = (i - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((Zlength ((app (l_done_2) ((replace_Znth (((i - 1 ) - (i - 1 ) )) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl high_limb tnc)) (32)))) ((sublist ((i - 1 )) (i) (l_up_inplace)))))))) = i)
.

Definition mpn_rshift_entail_wit_6_inplace := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 i l_done_2 )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  EX (l_done: (@list Z)) ,
  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  TT && emp 
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - 1 )) ”
  &&  emp
).

Definition mpn_rshift_entail_wit_6_inplace_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))
.

Definition mpn_rshift_entail_wit_6_inplace_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i >= (n_pre - 1 ))) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done_2)) = i)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done_2 )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((Zlength (l_done_2)) = (n_pre - 1 ))
.

Definition mpn_rshift_return_wit_1_inplace := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : ((Zlength (l_up_inplace)) = n_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (i = (n_pre - 1 ))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH13 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH14 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH15 : ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH16 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre i (i + 1 ) (replace_Znth ((i - i )) (low_limb) ((sublist (i) ((i + 1 )) (l_up_inplace)))) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 i l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_up_inplace)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : ((Zlength (l_up_inplace)) = n_pre)) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (i = (n_pre - 1 ))) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH13 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH14 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH15 : ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH16 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre i (i + 1 ) (replace_Znth ((i - i )) (low_limb) ((sublist (i) ((i + 1 )) (l_up_inplace)))) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 i l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_up_inplace)) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
).

Definition mpn_rshift_partial_solve_wit_1_inplace := 
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
  &&  (((up_pre + (0 * sizeof(UINT)))) # UInt  |-> (Znth 0 l_up_inplace 0))
  **  (UIntArray.missing_i up_pre 0 0 n_pre l_up_inplace )
.

Definition mpn_rshift_partial_solve_wit_2_inplace_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "retval" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth 0 l_up_inplace 0) (32 - cnt_pre ))) (32)))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Z.shiftr (Znth 0 l_up_inplace 0) cnt_pre))
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth 0 l_up_inplace 0))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
.

Definition mpn_rshift_partial_solve_wit_2_inplace_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (PreH1 : (rp_pre = up_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_up_inplace )) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.full up_pre n_pre l_up_inplace )
.

Definition mpn_rshift_partial_solve_wit_2_inplace := mpn_rshift_partial_solve_wit_2_inplace_pure -> mpn_rshift_partial_solve_wit_2_inplace_aux.

Definition mpn_rshift_partial_solve_wit_3_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i < (n_pre - 1 ))) (PreH2 : (tnc = (32 - cnt_pre ))) (PreH3 : (1 <= cnt_pre)) (PreH4 : (cnt_pre < 32)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = i)) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  “ (i < (n_pre - 1 )) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (((up_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((i + 1 ) - i ) (sublist (i) (n_pre) (l_up_inplace)) 0))
  **  (UIntArray.missing_i up_pre (i + 1 ) i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 i l_done )
.

Definition mpn_rshift_partial_solve_wit_4_inplace_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : ((Zlength (l_done)) = (i - 1 ))) (PreH8 : (list_within_bound UINT_MOD l_up_inplace )) (PreH9 : (list_within_bound UINT_MOD l_done )) (PreH10 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH11 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH12 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH13 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH14 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done )
  **  (UIntArray.seg up_pre (i - 1 ) n_pre (sublist ((i - 1 )) (n_pre) (l_up_inplace)) )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
.

Definition mpn_rshift_partial_solve_wit_4_inplace_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (1 <= i)) (PreH5 : (i < n_pre)) (PreH6 : ((Zlength (l_up_inplace)) = n_pre)) (PreH7 : ((Zlength (l_done)) = (i - 1 ))) (PreH8 : (list_within_bound UINT_MOD l_up_inplace )) (PreH9 : (list_within_bound UINT_MOD l_done )) (PreH10 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH11 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH12 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH13 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH14 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done )
  **  (UIntArray.seg up_pre (i - 1 ) n_pre (sublist ((i - 1 )) (n_pre) (l_up_inplace)) )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (i - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre (i - 1 ) n_pre (sublist ((i - 1 )) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done )
.

Definition mpn_rshift_partial_solve_wit_4_inplace := mpn_rshift_partial_solve_wit_4_inplace_pure -> mpn_rshift_partial_solve_wit_4_inplace_aux.

Definition mpn_rshift_partial_solve_wit_5_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (1 <= i)) (PreH7 : (i < n_pre)) (PreH8 : ((Zlength (l_up_inplace)) = n_pre)) (PreH9 : ((Zlength (l_done)) = (i - 1 ))) (PreH10 : (list_within_bound UINT_MOD l_up_inplace )) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH13 : (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH14 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH15 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH16 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre (i - 1 ) i (sublist ((i - 1 )) (i) (l_up_inplace)) )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done )
|--
  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (i - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (low_limb = ((Znth ((i - 1 )) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((i - 1 ))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (((up_pre + ((i - 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre (i - 1 ) (i - 1 ) i (sublist ((i - 1 )) (i) (l_up_inplace)) )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 (i - 1 ) l_done )
.

Definition mpn_rshift_partial_solve_wit_6_inplace_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (i = (n_pre - 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
.

Definition mpn_rshift_partial_solve_wit_6_inplace_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (tnc = (32 - cnt_pre ))) (PreH2 : (1 <= cnt_pre)) (PreH3 : (cnt_pre < 32)) (PreH4 : (i = (n_pre - 1 ))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : ((Zlength (l_up_inplace)) = n_pre)) (PreH8 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH9 : (list_within_bound UINT_MOD l_up_inplace )) (PreH10 : (list_within_bound UINT_MOD l_done )) (PreH11 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH12 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH13 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH14 : ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH15 : (rp_pre = up_pre)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 i l_done )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 i l_done )
.

Definition mpn_rshift_partial_solve_wit_6_inplace := mpn_rshift_partial_solve_wit_6_inplace_pure -> mpn_rshift_partial_solve_wit_6_inplace_aux.

Definition mpn_rshift_partial_solve_wit_7_inplace := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up_inplace: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : ((Zlength (l_up_inplace)) = n_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (i = (n_pre - 1 ))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_inplace)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_inplace )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (high_limb = (Znth (i) (l_up_inplace) (0)))) (PreH14 : (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH15 : (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH16 : ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) (PreH17 : (rp_pre = up_pre)) ,
  (UIntArray.seg up_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 i l_done )
|--
  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_inplace ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth (i) (l_up_inplace) (0))) ” 
  &&  “ (low_limb = ((Znth (i) (l_up_inplace) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (0) (l_up_inplace) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (n_pre) (l_up_inplace)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ” 
  &&  “ (rp_pre = up_pre) ”
  &&  (((up_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre i i (i + 1 ) (sublist (i) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_up_inplace)) )
  **  (UIntArray.seg up_pre 0 i l_done )
.

Definition mpn_rshift_which_implies_wit_1 := 
(
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (i = 0)) (PreH3 : (n_pre > 0)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  “ (rp = up_pre) ” 
  &&  “ (i = 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  (UIntArray.seg up_pre 0 0 (@nil Z) )
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
) \/
(
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (i = 0)) (PreH3 : (n_pre > 0)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
).

Definition mpn_rshift_which_implies_wit_1_split_goal_spatial := 
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (i = 0)) (PreH3 : (n_pre > 0)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  (UIntArray.full up_pre n_pre l_up_inplace )
|--
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_inplace)) )
.

Definition mpn_rshift_which_implies_wit_2 := 
(
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (1 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  (UIntArray.seg up_pre (i - 1 ) n_pre (sublist ((i - 1 )) (n_pre) (l_up_inplace)) )
|--
  “ (rp = up_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  (UIntArray.seg up_pre (i - 1 ) i (sublist ((i - 1 )) (i) (l_up_inplace)) )
  **  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
) \/
(
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (1 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  TT && emp 
|--
  “ ((sublist ((i - 1 )) (n_pre) (l_up_inplace)) = (app ((sublist ((i - 1 )) (i) (l_up_inplace))) ((sublist (i) (n_pre) (l_up_inplace))))) ” 
  &&  “ ((Zlength ((sublist ((i - 1 )) (i) (l_up_inplace)))) = (i - (i - 1 ) )) ”
  &&  emp
).

Definition mpn_rshift_which_implies_wit_2_split_goal_1 := 
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (1 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  ((sublist ((i - 1 )) (n_pre) (l_up_inplace)) = (app ((sublist ((i - 1 )) (i) (l_up_inplace))) ((sublist (i) (n_pre) (l_up_inplace)))))
.

Definition mpn_rshift_which_implies_wit_2_split_goal_2 := 
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (1 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  ((Zlength ((sublist ((i - 1 )) (i) (l_up_inplace)))) = (i - (i - 1 ) ))
.

Definition mpn_rshift_which_implies_wit_3 := 
(
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  (UIntArray.seg up_pre i n_pre (sublist (i) (n_pre) (l_up_inplace)) )
|--
  “ (rp = up_pre) ” 
  &&  “ ((Zlength (l_up_inplace)) = n_pre) ”
  &&  (UIntArray.seg up_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_up_inplace)) )
  **  (UIntArray.seg up_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_up_inplace)) )
) \/
(
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  TT && emp 
|--
  “ ((sublist (i) (n_pre) (l_up_inplace)) = (app ((sublist (i) ((i + 1 )) (l_up_inplace))) ((sublist ((i + 1 )) (n_pre) (l_up_inplace))))) ” 
  &&  “ ((Zlength ((sublist (i) ((i + 1 )) (l_up_inplace)))) = ((i + 1 ) - i )) ”
  &&  emp
).

Definition mpn_rshift_which_implies_wit_3_split_goal_1 := 
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  ((sublist (i) (n_pre) (l_up_inplace)) = (app ((sublist (i) ((i + 1 )) (l_up_inplace))) ((sublist ((i + 1 )) (n_pre) (l_up_inplace)))))
.

Definition mpn_rshift_which_implies_wit_3_split_goal_2 := 
forall (n_pre: Z) (up_pre: Z) (l_up_inplace: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_up_inplace)) = n_pre)) ,
  ((Zlength ((sublist (i) ((i + 1 )) (l_up_inplace)))) = ((i + 1 ) - i ))
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_rshift_safety_wit_1_inplace : mpn_rshift_safety_wit_1_inplace.
Axiom proof_of_mpn_rshift_safety_wit_2_inplace : mpn_rshift_safety_wit_2_inplace.
Axiom proof_of_mpn_rshift_safety_wit_3_inplace : mpn_rshift_safety_wit_3_inplace.
Axiom proof_of_mpn_rshift_safety_wit_4_inplace : mpn_rshift_safety_wit_4_inplace.
Axiom proof_of_mpn_rshift_safety_wit_5_inplace : mpn_rshift_safety_wit_5_inplace.
Axiom proof_of_mpn_rshift_safety_wit_6_inplace : mpn_rshift_safety_wit_6_inplace.
Axiom proof_of_mpn_rshift_safety_wit_7_inplace : mpn_rshift_safety_wit_7_inplace.
Axiom proof_of_mpn_rshift_safety_wit_8_inplace : mpn_rshift_safety_wit_8_inplace.
Axiom proof_of_mpn_rshift_safety_wit_9_inplace : mpn_rshift_safety_wit_9_inplace.
Axiom proof_of_mpn_rshift_safety_wit_10_inplace : mpn_rshift_safety_wit_10_inplace.
Axiom proof_of_mpn_rshift_safety_wit_11_inplace : mpn_rshift_safety_wit_11_inplace.
Axiom proof_of_mpn_rshift_safety_wit_12_inplace : mpn_rshift_safety_wit_12_inplace.
Axiom proof_of_mpn_rshift_entail_wit_1_inplace : mpn_rshift_entail_wit_1_inplace.
Axiom proof_of_mpn_rshift_entail_wit_2_inplace : mpn_rshift_entail_wit_2_inplace.
Axiom proof_of_mpn_rshift_entail_wit_3_inplace : mpn_rshift_entail_wit_3_inplace.
Axiom proof_of_mpn_rshift_entail_wit_4_inplace : mpn_rshift_entail_wit_4_inplace.
Axiom proof_of_mpn_rshift_entail_wit_5_inplace : mpn_rshift_entail_wit_5_inplace.
Axiom proof_of_mpn_rshift_entail_wit_6_inplace : mpn_rshift_entail_wit_6_inplace.
Axiom proof_of_mpn_rshift_return_wit_1_inplace : mpn_rshift_return_wit_1_inplace.
Axiom proof_of_mpn_rshift_partial_solve_wit_1_inplace : mpn_rshift_partial_solve_wit_1_inplace.
Axiom proof_of_mpn_rshift_partial_solve_wit_2_inplace_pure : mpn_rshift_partial_solve_wit_2_inplace_pure.
Axiom proof_of_mpn_rshift_partial_solve_wit_2_inplace : mpn_rshift_partial_solve_wit_2_inplace.
Axiom proof_of_mpn_rshift_partial_solve_wit_3_inplace : mpn_rshift_partial_solve_wit_3_inplace.
Axiom proof_of_mpn_rshift_partial_solve_wit_4_inplace_pure : mpn_rshift_partial_solve_wit_4_inplace_pure.
Axiom proof_of_mpn_rshift_partial_solve_wit_4_inplace : mpn_rshift_partial_solve_wit_4_inplace.
Axiom proof_of_mpn_rshift_partial_solve_wit_5_inplace : mpn_rshift_partial_solve_wit_5_inplace.
Axiom proof_of_mpn_rshift_partial_solve_wit_6_inplace_pure : mpn_rshift_partial_solve_wit_6_inplace_pure.
Axiom proof_of_mpn_rshift_partial_solve_wit_6_inplace : mpn_rshift_partial_solve_wit_6_inplace.
Axiom proof_of_mpn_rshift_partial_solve_wit_7_inplace : mpn_rshift_partial_solve_wit_7_inplace.
Axiom proof_of_mpn_rshift_which_implies_wit_1 : mpn_rshift_which_implies_wit_1.
Axiom proof_of_mpn_rshift_which_implies_wit_2 : mpn_rshift_which_implies_wit_2.
Axiom proof_of_mpn_rshift_which_implies_wit_3 : mpn_rshift_which_implies_wit_3.

End VC_Correct.
