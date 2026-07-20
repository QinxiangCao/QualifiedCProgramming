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

(*----- Function mpn_add_n -----*)

Definition mpn_add_n_safety_wit_1_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_b: (@list Z)) (l_a: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH4 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH5 : (list_within_bound UINT_MOD l_a )) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (rp_pre = bp_pre)) (PreH8 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_n_safety_wit_2_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_b: (@list Z)) (l_a: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH4 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH5 : (list_within_bound UINT_MOD l_a )) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_n_safety_wit_3_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_b: (@list Z)) (l_a: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH4 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH5 : (list_within_bound UINT_MOD l_a )) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (rp_pre = bp_pre)) (PreH8 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_n_safety_wit_4_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_b: (@list Z)) (l_a: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH4 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH5 : (list_within_bound UINT_MOD l_a )) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_n_safety_wit_5_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_6_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_7_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_8_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_9_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0))
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_10_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0))
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_11_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0))
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_safety_wit_12_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0))
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_n_entail_wit_1_rp_eq_bp := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (rp_pre = rp_pre)) (PreH2 : (n_pre >= 0)) (PreH3 : ((Zlength (l_a)) = n_pre)) (PreH4 : ((Zlength (l_b)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH6 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH7 : (list_within_bound UINT_MOD l_a )) (PreH8 : (list_within_bound UINT_MOD l_b )) (PreH9 : (rp_pre = bp_pre)) (PreH10 : (n_pre >= 0)) ,
  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg rp_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (0 * (Z.pow (UINT_MOD) (0)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.seg rp_pre 0 0 l_r )
  **  (UIntArray.seg rp_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (n_pre >= 0)) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) )) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  emp
).

Definition mpn_add_n_entail_wit_1_rp_eq_bp_split_goal_1 := 
forall (n_pre: Z) (bp_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (n_pre >= 0)) ,
  (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) ))
.

Definition mpn_add_n_entail_wit_1_rp_eq_bp_split_goal_2 := 
forall (n_pre: Z) (bp_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (n_pre >= 0)) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition mpn_add_n_entail_wit_1_rp_eq_bp_split_goal_3 := 
forall (n_pre: Z) (bp_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (n_pre >= 0)) ,
  (list_within_bound UINT_MOD (@nil Z) )
.

Definition mpn_add_n_entail_wit_2_rp_eq_ap := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (rp_pre = rp_pre)) (PreH2 : (n_pre >= 0)) (PreH3 : ((Zlength (l_a)) = n_pre)) (PreH4 : ((Zlength (l_b)) = n_pre)) (PreH5 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH6 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH7 : (list_within_bound UINT_MOD l_a )) (PreH8 : (list_within_bound UINT_MOD l_b )) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (n_pre >= 0)) ,
  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg rp_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (0 * (Z.pow (UINT_MOD) (0)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg rp_pre 0 0 l_r )
  **  (UIntArray.seg rp_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = ap_pre)) (PreH9 : (n_pre >= 0)) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) )) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ”
  &&  emp
).

Definition mpn_add_n_entail_wit_2_rp_eq_ap_split_goal_1 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = ap_pre)) (PreH9 : (n_pre >= 0)) ,
  (((list_to_Z (UINT_MOD) ((@nil Z))) + (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) (0) (l_b)))) ))
.

Definition mpn_add_n_entail_wit_2_rp_eq_ap_split_goal_2 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = ap_pre)) (PreH9 : (n_pre >= 0)) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition mpn_add_n_entail_wit_2_rp_eq_ap_split_goal_3 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = ap_pre)) (PreH9 : (n_pre >= 0)) ,
  (list_within_bound UINT_MOD (@nil Z) )
.

Definition mpn_add_n_entail_wit_3_1_rp_eq_bp := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 0 )) ” 
  &&  “ ((0 + 0 ) <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (l_r: (@list Z)) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 0 )) ” 
  &&  “ ((0 + 0 ) <= 2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_r)) + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_b)) )
).

Definition mpn_add_n_entail_wit_3_2_rp_eq_bp := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (l_r: (@list Z)) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= 2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_r)) + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_b)) )
).

Definition mpn_add_n_entail_wit_3_3_rp_eq_bp := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 0 )) ” 
  &&  “ ((1 + 0 ) <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (l_r: (@list Z)) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 0 )) ” 
  &&  “ ((1 + 0 ) <= 2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_r)) + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_b)) )
).

Definition mpn_add_n_entail_wit_3_4_rp_eq_bp := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 1 )) ” 
  &&  “ ((1 + 1 ) <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_b)))) )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (l_r: (@list Z)) ,
  “ (rp_pre = bp_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 1 )) ” 
  &&  “ ((1 + 1 ) <= 2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_r)) + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_b)) )
).

Definition mpn_add_n_entail_wit_4_1_rp_eq_ap := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 0 )) ” 
  &&  “ ((0 + 0 ) <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (l_r: (@list Z)) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 0 )) ” 
  &&  “ ((0 + 0 ) <= 2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_r)) + ((0 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_a)) )
).

Definition mpn_add_n_entail_wit_4_2_rp_eq_ap := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (l_r: (@list Z)) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= 2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_r)) + ((0 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_a)) )
).

Definition mpn_add_n_entail_wit_4_3_rp_eq_ap := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 0 )) ” 
  &&  “ ((1 + 0 ) <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (l_r: (@list Z)) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 0 )) ” 
  &&  “ ((1 + 0 ) <= 2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_r)) + ((1 + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_a)) )
).

Definition mpn_add_n_entail_wit_4_4_rp_eq_ap := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (val_r: Z)  (l_r: (@list Z))  (val_b_prefix: Z)  (val_a_prefix: Z) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 1 )) ” 
  &&  “ ((1 + 1 ) <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r_2: Z) (l_r_2: (@list Z)) (val_b_prefix_2: Z) (val_a_prefix_2: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix_2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix_2)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r_2)) = val_r_2)) (PreH13 : (list_within_bound UINT_MOD l_r_2 )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r_2)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r_2 + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix_2 + val_b_prefix_2 ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32))) ((sublist (i) ((Zlength (l_a))) (l_a)))) )
  **  (UIntArray.seg rp_pre 0 i l_r_2 )
|--
  EX (l_r: (@list Z)) ,
  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (1 + 1 )) ” 
  &&  “ ((1 + 1 ) <= 2) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_r)) + ((1 + 1 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_a)))) + (list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_b)))) )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_r )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l_a)) (sublist ((i + 1 )) ((Zlength (l_a))) (l_a)) )
).

Definition mpn_add_n_return_wit_1_rp_eq_bp := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = bp_pre)) (PreH26 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a_rp_eq_bp + val_b_rp_eq_bp )) ” 
  &&  “ (rp_pre = bp_pre) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out n_pre )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = bp_pre)) (PreH26 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a_rp_eq_bp + val_b_rp_eq_bp )) ” 
  &&  “ (rp_pre = bp_pre) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val_r_out n_pre )
).

Definition mpn_add_n_return_wit_2_rp_eq_ap := 
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = ap_pre)) (PreH26 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a_rp_eq_ap + val_b_rp_eq_ap )) ” 
  &&  “ (rp_pre = ap_pre) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val_r_out n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap n_pre )
) \/
(
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = ap_pre)) (PreH26 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  EX (val_r_out: Z) ,
  “ ((val_r_out + (cy * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_a_rp_eq_ap + val_b_rp_eq_ap )) ” 
  &&  “ (rp_pre = ap_pre) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val_r_out n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap n_pre )
).

Definition mpn_add_n_partial_solve_wit_1_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (n_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_ap n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap n_pre )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_ap n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_ap n_pre )
.

Definition mpn_add_n_partial_solve_wit_2_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (PreH1 : (rp_pre = bp_pre)) (PreH2 : (n_pre >= 0)) ,
  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_bp n_pre )
|--
  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_a_rp_eq_bp n_pre )
  **  (mpd_store_Z UINT_MOD bp_pre val_b_rp_eq_bp n_pre )
.

Definition mpn_add_n_partial_solve_wit_3_rp_eq_ap_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH4 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH5 : (list_within_bound UINT_MOD l_a )) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (n_pre >= 0) ”
.

Definition mpn_add_n_partial_solve_wit_3_rp_eq_ap_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH4 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH5 : (list_within_bound UINT_MOD l_a )) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre >= 0)) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_partial_solve_wit_3_rp_eq_ap := mpn_add_n_partial_solve_wit_3_rp_eq_ap_pure -> mpn_add_n_partial_solve_wit_3_rp_eq_ap_aux.

Definition mpn_add_n_partial_solve_wit_4_rp_eq_bp_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH4 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH5 : (list_within_bound UINT_MOD l_a )) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (rp_pre = bp_pre)) (PreH8 : (n_pre >= 0)) ,
  ((( &( "cy" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ”
.

Definition mpn_add_n_partial_solve_wit_4_rp_eq_bp_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : ((Zlength (l_a)) = n_pre)) (PreH2 : ((Zlength (l_b)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH4 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH5 : (list_within_bound UINT_MOD l_a )) (PreH6 : (list_within_bound UINT_MOD l_b )) (PreH7 : (rp_pre = bp_pre)) (PreH8 : (n_pre >= 0)) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.full ap_pre n_pre l_a )
.

Definition mpn_add_n_partial_solve_wit_4_rp_eq_bp := mpn_add_n_partial_solve_wit_4_rp_eq_bp_pure -> mpn_add_n_partial_solve_wit_4_rp_eq_bp_aux.

Definition mpn_add_n_partial_solve_wit_5_rp_eq_ap_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = ap_pre)) (PreH9 : (n_pre >= 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg ap_pre 0 0 (@nil Z) )
  **  (UIntArray.seg ap_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
  **  ((( &( "cy" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.full bp_pre n_pre l_b )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_5_rp_eq_ap_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = ap_pre)) (PreH9 : (n_pre >= 0)) ,
  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg ap_pre 0 0 (@nil Z) )
  **  (UIntArray.seg ap_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg rp_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_partial_solve_wit_5_rp_eq_ap := mpn_add_n_partial_solve_wit_5_rp_eq_ap_pure -> mpn_add_n_partial_solve_wit_5_rp_eq_ap_aux.

Definition mpn_add_n_partial_solve_wit_6_rp_eq_bp_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (n_pre >= 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.seg bp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg bp_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
  **  ((( &( "cy" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_6_rp_eq_bp_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l_a)) = n_pre)) (PreH3 : ((Zlength (l_b)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH5 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH6 : (list_within_bound UINT_MOD l_a )) (PreH7 : (list_within_bound UINT_MOD l_b )) (PreH8 : (rp_pre = bp_pre)) (PreH9 : (n_pre >= 0)) ,
  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.seg bp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg bp_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg rp_pre 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
.

Definition mpn_add_n_partial_solve_wit_6_rp_eq_bp := mpn_add_n_partial_solve_wit_6_rp_eq_bp_pure -> mpn_add_n_partial_solve_wit_6_rp_eq_bp_aux.

Definition mpn_add_n_partial_solve_wit_7_rp_eq_ap_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = ap_pre)) (PreH26 : (n_pre >= 0)) ,
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "b" ) )) # UInt  |->_)
  **  ((( &( "a" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_7_rp_eq_ap_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = ap_pre)) (PreH26 : (n_pre >= 0)) ,
  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_partial_solve_wit_7_rp_eq_ap := mpn_add_n_partial_solve_wit_7_rp_eq_ap_pure -> mpn_add_n_partial_solve_wit_7_rp_eq_ap_aux.

Definition mpn_add_n_partial_solve_wit_8_rp_eq_bp_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = bp_pre)) (PreH26 : (n_pre >= 0)) ,
  ((( &( "r" ) )) # UInt  |->_)
  **  ((( &( "b" ) )) # UInt  |->_)
  **  ((( &( "a" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cy" ) )) # UInt  |-> cy)
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_8_rp_eq_bp_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = bp_pre)) (PreH26 : (n_pre >= 0)) ,
  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.full ap_pre n_pre l_a )
.

Definition mpn_add_n_partial_solve_wit_8_rp_eq_bp := mpn_add_n_partial_solve_wit_8_rp_eq_bp_pure -> mpn_add_n_partial_solve_wit_8_rp_eq_bp_aux.

Definition mpn_add_n_partial_solve_wit_9_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : (i < n_pre)) (PreH3 : (rp_pre = bp_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= cy)) (PreH8 : (cy <= 2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH12 : (list_within_bound UINT_MOD l_r )) (PreH13 : (list_within_bound UINT_MOD l_a )) (PreH14 : (list_within_bound UINT_MOD l_b )) (PreH15 : ((Zlength (l_r)) = i)) (PreH16 : ((Zlength (l_a)) = n_pre)) (PreH17 : ((Zlength (l_b)) = n_pre)) (PreH18 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH19 : (n_pre >= 0)) (PreH20 : ((Zlength (l_a)) = n_pre)) (PreH21 : ((Zlength (l_b)) = n_pre)) (PreH22 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH23 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH24 : (list_within_bound UINT_MOD l_a )) (PreH25 : (list_within_bound UINT_MOD l_b )) (PreH26 : (rp_pre = bp_pre)) (PreH27 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.full ap_pre n_pre l_a )
|--
  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((ap_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_a 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l_a )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_10_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : (i < n_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= cy)) (PreH8 : (cy <= 2)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH12 : (list_within_bound UINT_MOD l_r )) (PreH13 : (list_within_bound UINT_MOD l_a )) (PreH14 : (list_within_bound UINT_MOD l_b )) (PreH15 : ((Zlength (l_r)) = i)) (PreH16 : ((Zlength (l_a)) = n_pre)) (PreH17 : ((Zlength (l_b)) = n_pre)) (PreH18 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH19 : (n_pre >= 0)) (PreH20 : ((Zlength (l_a)) = n_pre)) (PreH21 : ((Zlength (l_b)) = n_pre)) (PreH22 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH23 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH24 : (list_within_bound UINT_MOD l_a )) (PreH25 : (list_within_bound UINT_MOD l_b )) (PreH26 : (rp_pre = ap_pre)) (PreH27 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0))
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.full bp_pre n_pre l_b )
.

Definition mpn_add_n_partial_solve_wit_11_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (rp_pre = bp_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = bp_pre)) (PreH26 : (n_pre >= 0)) ,
  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_12_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cy)) (PreH7 : (cy <= 2)) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH10 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH11 : (list_within_bound UINT_MOD l_r )) (PreH12 : (list_within_bound UINT_MOD l_a )) (PreH13 : (list_within_bound UINT_MOD l_b )) (PreH14 : ((Zlength (l_r)) = i)) (PreH15 : ((Zlength (l_a)) = n_pre)) (PreH16 : ((Zlength (l_b)) = n_pre)) (PreH17 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH18 : (n_pre >= 0)) (PreH19 : ((Zlength (l_a)) = n_pre)) (PreH20 : ((Zlength (l_b)) = n_pre)) (PreH21 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH22 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH23 : (list_within_bound UINT_MOD l_a )) (PreH24 : (list_within_bound UINT_MOD l_b )) (PreH25 : (rp_pre = ap_pre)) (PreH26 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
  **  (UIntArray.full bp_pre n_pre l_b )
|--
  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((bp_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_b 0))
  **  (UIntArray.missing_i bp_pre i 0 n_pre l_b )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_13_rp_eq_ap_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0))
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_13_rp_eq_ap_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_13_rp_eq_ap := mpn_add_n_partial_solve_wit_13_rp_eq_ap_pure -> mpn_add_n_partial_solve_wit_13_rp_eq_ap_aux.

Definition mpn_add_n_partial_solve_wit_14_rp_eq_ap_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0))
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_14_rp_eq_ap_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_14_rp_eq_ap := mpn_add_n_partial_solve_wit_14_rp_eq_ap_pure -> mpn_add_n_partial_solve_wit_14_rp_eq_ap_aux.

Definition mpn_add_n_partial_solve_wit_15_rp_eq_ap_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0))
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_15_rp_eq_ap_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_15_rp_eq_ap := mpn_add_n_partial_solve_wit_15_rp_eq_ap_pure -> mpn_add_n_partial_solve_wit_15_rp_eq_ap_aux.

Definition mpn_add_n_partial_solve_wit_16_rp_eq_ap_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth i l_b 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0))
  **  ((( &( "bp" ) )) # Ptr  |-> bp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_16_rp_eq_ap_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH2 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = ap_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_16_rp_eq_ap := mpn_add_n_partial_solve_wit_16_rp_eq_ap_pure -> mpn_add_n_partial_solve_wit_16_rp_eq_ap_aux.

Definition mpn_add_n_partial_solve_wit_17_rp_eq_bp_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 1 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_17_rp_eq_bp_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_17_rp_eq_bp := mpn_add_n_partial_solve_wit_17_rp_eq_bp_pure -> mpn_add_n_partial_solve_wit_17_rp_eq_bp_aux.

Definition mpn_add_n_partial_solve_wit_18_rp_eq_bp_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (1 + 0 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_18_rp_eq_bp_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_18_rp_eq_bp := mpn_add_n_partial_solve_wit_18_rp_eq_bp_pure -> mpn_add_n_partial_solve_wit_18_rp_eq_bp_aux.

Definition mpn_add_n_partial_solve_wit_19_rp_eq_bp_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 1 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_19_rp_eq_bp_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_19_rp_eq_bp := mpn_add_n_partial_solve_wit_19_rp_eq_bp_pure -> mpn_add_n_partial_solve_wit_19_rp_eq_bp_aux.

Definition mpn_add_n_partial_solve_wit_20_rp_eq_bp_pure := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "bp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))
  **  ((( &( "a" ) )) # UInt  |-> (Znth i l_a 0))
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cy" ) )) # UInt  |-> (0 + 0 ))
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_n_partial_solve_wit_20_rp_eq_bp_aux := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH2 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH3 : (i < n_pre)) (PreH4 : (rp_pre = bp_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= cy)) (PreH9 : (cy <= 2)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH13 : (list_within_bound UINT_MOD l_r )) (PreH14 : (list_within_bound UINT_MOD l_a )) (PreH15 : (list_within_bound UINT_MOD l_b )) (PreH16 : ((Zlength (l_r)) = i)) (PreH17 : ((Zlength (l_a)) = n_pre)) (PreH18 : ((Zlength (l_b)) = n_pre)) (PreH19 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH20 : (n_pre >= 0)) (PreH21 : ((Zlength (l_a)) = n_pre)) (PreH22 : ((Zlength (l_b)) = n_pre)) (PreH23 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH24 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH25 : (list_within_bound UINT_MOD l_a )) (PreH26 : (list_within_bound UINT_MOD l_b )) (PreH27 : (rp_pre = bp_pre)) (PreH28 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_20_rp_eq_bp := mpn_add_n_partial_solve_wit_20_rp_eq_bp_pure -> mpn_add_n_partial_solve_wit_20_rp_eq_bp_aux.

Definition mpn_add_n_partial_solve_wit_21_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH3 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH4 : (i < n_pre)) (PreH5 : (rp_pre = bp_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= 2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH13 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH14 : (list_within_bound UINT_MOD l_r )) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : (list_within_bound UINT_MOD l_b )) (PreH17 : ((Zlength (l_r)) = i)) (PreH18 : ((Zlength (l_a)) = n_pre)) (PreH19 : ((Zlength (l_b)) = n_pre)) (PreH20 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH21 : (n_pre >= 0)) (PreH22 : ((Zlength (l_a)) = n_pre)) (PreH23 : ((Zlength (l_b)) = n_pre)) (PreH24 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH25 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH26 : (list_within_bound UINT_MOD l_a )) (PreH27 : (list_within_bound UINT_MOD l_b )) (PreH28 : (rp_pre = bp_pre)) (PreH29 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_22_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH3 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy)) (PreH4 : (i < n_pre)) (PreH5 : (rp_pre = bp_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= 2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH13 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH14 : (list_within_bound UINT_MOD l_r )) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : (list_within_bound UINT_MOD l_b )) (PreH17 : ((Zlength (l_r)) = i)) (PreH18 : ((Zlength (l_a)) = n_pre)) (PreH19 : ((Zlength (l_b)) = n_pre)) (PreH20 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH21 : (n_pre >= 0)) (PreH22 : ((Zlength (l_a)) = n_pre)) (PreH23 : ((Zlength (l_b)) = n_pre)) (PreH24 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH25 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH26 : (list_within_bound UINT_MOD l_a )) (PreH27 : (list_within_bound UINT_MOD l_b )) (PreH28 : (rp_pre = bp_pre)) (PreH29 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_23_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH3 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH4 : (i < n_pre)) (PreH5 : (rp_pre = bp_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= 2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH13 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH14 : (list_within_bound UINT_MOD l_r )) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : (list_within_bound UINT_MOD l_b )) (PreH17 : ((Zlength (l_r)) = i)) (PreH18 : ((Zlength (l_a)) = n_pre)) (PreH19 : ((Zlength (l_b)) = n_pre)) (PreH20 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH21 : (n_pre >= 0)) (PreH22 : ((Zlength (l_a)) = n_pre)) (PreH23 : ((Zlength (l_b)) = n_pre)) (PreH24 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH25 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH26 : (list_within_bound UINT_MOD l_a )) (PreH27 : (list_within_bound UINT_MOD l_b )) (PreH28 : (rp_pre = bp_pre)) (PreH29 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) >= (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_24_rp_eq_bp := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0))) (PreH3 : ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy)) (PreH4 : (i < n_pre)) (PreH5 : (rp_pre = bp_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= 2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH13 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH14 : (list_within_bound UINT_MOD l_r )) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : (list_within_bound UINT_MOD l_b )) (PreH17 : ((Zlength (l_r)) = i)) (PreH18 : ((Zlength (l_a)) = n_pre)) (PreH19 : ((Zlength (l_b)) = n_pre)) (PreH20 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH21 : (n_pre >= 0)) (PreH22 : ((Zlength (l_a)) = n_pre)) (PreH23 : ((Zlength (l_b)) = n_pre)) (PreH24 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp)) (PreH25 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp)) (PreH26 : (list_within_bound UINT_MOD l_a )) (PreH27 : (list_within_bound UINT_MOD l_b )) (PreH28 : (rp_pre = bp_pre)) (PreH29 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) + (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0) )) (32)) < (Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_b)) 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth i l_a 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = bp_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
  **  (UIntArray.full ap_pre n_pre l_a )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_25_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH3 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH4 : (i < n_pre)) (PreH5 : (rp_pre = ap_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= 2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH13 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH14 : (list_within_bound UINT_MOD l_r )) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : (list_within_bound UINT_MOD l_b )) (PreH17 : ((Zlength (l_r)) = i)) (PreH18 : ((Zlength (l_a)) = n_pre)) (PreH19 : ((Zlength (l_b)) = n_pre)) (PreH20 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH21 : (n_pre >= 0)) (PreH22 : ((Zlength (l_a)) = n_pre)) (PreH23 : ((Zlength (l_b)) = n_pre)) (PreH24 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH25 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH26 : (list_within_bound UINT_MOD l_a )) (PreH27 : (list_within_bound UINT_MOD l_b )) (PreH28 : (rp_pre = ap_pre)) (PreH29 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_26_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH3 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy)) (PreH4 : (i < n_pre)) (PreH5 : (rp_pre = ap_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= 2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH13 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH14 : (list_within_bound UINT_MOD l_r )) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : (list_within_bound UINT_MOD l_b )) (PreH17 : ((Zlength (l_r)) = i)) (PreH18 : ((Zlength (l_a)) = n_pre)) (PreH19 : ((Zlength (l_b)) = n_pre)) (PreH20 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH21 : (n_pre >= 0)) (PreH22 : ((Zlength (l_a)) = n_pre)) (PreH23 : ((Zlength (l_b)) = n_pre)) (PreH24 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH25 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH26 : (list_within_bound UINT_MOD l_a )) (PreH27 : (list_within_bound UINT_MOD l_b )) (PreH28 : (rp_pre = ap_pre)) (PreH29 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) >= cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_27_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0))) (PreH3 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH4 : (i < n_pre)) (PreH5 : (rp_pre = ap_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= 2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH13 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH14 : (list_within_bound UINT_MOD l_r )) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : (list_within_bound UINT_MOD l_b )) (PreH17 : ((Zlength (l_r)) = i)) (PreH18 : ((Zlength (l_a)) = n_pre)) (PreH19 : ((Zlength (l_b)) = n_pre)) (PreH20 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH21 : (n_pre >= 0)) (PreH22 : ((Zlength (l_a)) = n_pre)) (PreH23 : ((Zlength (l_b)) = n_pre)) (PreH24 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH25 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH26 : (list_within_bound UINT_MOD l_a )) (PreH27 : (list_within_bound UINT_MOD l_b )) (PreH28 : (rp_pre = ap_pre)) (PreH29 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) >= (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_partial_solve_wit_28_rp_eq_ap := 
forall (n_pre: Z) (bp_pre: Z) (ap_pre: Z) (rp_pre: Z) (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (l_a: (@list Z)) (l_b: (@list Z)) (val_r: Z) (l_r: (@list Z)) (val_b_prefix: Z) (val_a_prefix: Z) (cy: Z) (i: Z) (PreH1 : (rp_pre = rp_pre)) (PreH2 : ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0))) (PreH3 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy)) (PreH4 : (i < n_pre)) (PreH5 : (rp_pre = ap_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= cy)) (PreH10 : (cy <= 2)) (PreH11 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix)) (PreH13 : ((list_to_Z (UINT_MOD) (l_r)) = val_r)) (PreH14 : (list_within_bound UINT_MOD l_r )) (PreH15 : (list_within_bound UINT_MOD l_a )) (PreH16 : (list_within_bound UINT_MOD l_b )) (PreH17 : ((Zlength (l_r)) = i)) (PreH18 : ((Zlength (l_a)) = n_pre)) (PreH19 : ((Zlength (l_b)) = n_pre)) (PreH20 : ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix ))) (PreH21 : (n_pre >= 0)) (PreH22 : ((Zlength (l_a)) = n_pre)) (PreH23 : ((Zlength (l_b)) = n_pre)) (PreH24 : ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap)) (PreH25 : ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap)) (PreH26 : (list_within_bound UINT_MOD l_a )) (PreH27 : (list_within_bound UINT_MOD l_b )) (PreH28 : (rp_pre = ap_pre)) (PreH29 : (n_pre >= 0)) ,
  (UIntArray.seg rp_pre i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
|--
  “ ((unsigned_last_nbits (((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) + (Znth i l_b 0) )) (32)) < (Znth i l_b 0)) ” 
  &&  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l_a))) (l_a)) 0) + cy )) (32)) < cy) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cy) ” 
  &&  “ (cy <= 2) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_a)))) = val_a_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_b)))) = val_b_prefix) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_r)) = val_r) ” 
  &&  “ (list_within_bound UINT_MOD l_r ) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ ((Zlength (l_r)) = i) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((val_r + (cy * (Z.pow (UINT_MOD) (i)) ) ) = (val_a_prefix + val_b_prefix )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_a)) = n_pre) ” 
  &&  “ ((Zlength (l_b)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre >= 0) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
  **  (UIntArray.full bp_pre n_pre l_b )
  **  (UIntArray.seg rp_pre 0 i l_r )
.

Definition mpn_add_n_which_implies_wit_1 := 
(
forall (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a_rp_eq_ap n )
  **  (mpd_store_Z UINT_MOD bp val_b_rp_eq_ap n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
) \/
(
forall (val_b_rp_eq_ap: Z) (val_a_rp_eq_ap: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a_rp_eq_ap n )
  **  (mpd_store_Z UINT_MOD bp val_b_rp_eq_ap n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_ap) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
).

Definition mpn_add_n_which_implies_wit_2 := 
(
forall (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a_rp_eq_bp n )
  **  (mpd_store_Z UINT_MOD bp val_b_rp_eq_bp n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
) \/
(
forall (val_b_rp_eq_bp: Z) (val_a_rp_eq_bp: Z) (n: Z) (ap: Z) (bp: Z) ,
  (mpd_store_Z UINT_MOD ap val_a_rp_eq_bp n )
  **  (mpd_store_Z UINT_MOD bp val_b_rp_eq_bp n )
|--
  EX (l_b: (@list Z))  (l_a: (@list Z)) ,
  “ ((Zlength (l_a)) = n) ” 
  &&  “ ((Zlength (l_b)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_a)) = val_a_rp_eq_bp) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_b)) = val_b_rp_eq_bp) ” 
  &&  “ (list_within_bound UINT_MOD l_a ) ” 
  &&  “ (list_within_bound UINT_MOD l_b ) ”
  &&  (UIntArray.full ap n l_a )
  **  (UIntArray.full bp n l_b )
).

Definition mpn_add_n_which_implies_wit_3 := 
(
forall (l_a: (@list Z)) (n: Z) (ap: Z) (PreH1 : (n >= 0)) ,
  (UIntArray.full ap n l_a )
|--
  “ (n >= 0) ”
  &&  (UIntArray.seg ap 0 0 (@nil Z) )
  **  (UIntArray.seg ap 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
) \/
(
forall (l_a: (@list Z)) (n: Z) (ap: Z) (PreH1 : (n >= 0)) ,
  (UIntArray.full ap n l_a )
|--
  (UIntArray.seg ap 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
).

Definition mpn_add_n_which_implies_wit_3_split_goal_spatial := 
forall (l_a: (@list Z)) (n: Z) (ap: Z) (PreH1 : (n >= 0)) ,
  (UIntArray.full ap n l_a )
|--
  (UIntArray.seg ap 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
.

Definition mpn_add_n_which_implies_wit_4 := 
(
forall (l_a: (@list Z)) (l_b: (@list Z)) (n: Z) (bp: Z) (PreH1 : (n >= 0)) (PreH2 : ((Zlength (l_a)) = n)) ,
  (UIntArray.full bp n l_b )
|--
  “ (n >= 0) ”
  &&  (UIntArray.seg bp 0 0 (@nil Z) )
  **  (UIntArray.seg bp 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
) \/
(
forall (l_a: (@list Z)) (l_b: (@list Z)) (n: Z) (bp: Z) (PreH1 : (n >= 0)) (PreH2 : ((Zlength (l_a)) = n)) ,
  (UIntArray.full bp n l_b )
|--
  (UIntArray.seg bp 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
).

Definition mpn_add_n_which_implies_wit_4_split_goal_spatial := 
forall (l_a: (@list Z)) (l_b: (@list Z)) (n: Z) (bp: Z) (PreH1 : (n >= 0)) (PreH2 : ((Zlength (l_a)) = n)) ,
  (UIntArray.full bp n l_b )
|--
  (UIntArray.seg bp 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
.

Definition mpn_add_n_which_implies_wit_5 := 
forall (l_a: (@list Z)) (rp: Z) (ap: Z) (PreH1 : (rp = ap)) ,
  (UIntArray.seg ap 0 0 (@nil Z) )
  **  (UIntArray.seg ap 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
|--
  “ (rp = ap) ”
  &&  (UIntArray.seg rp 0 0 (@nil Z) )
  **  (UIntArray.seg rp 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_a)) )
.

Definition mpn_add_n_which_implies_wit_6 := 
forall (l_a: (@list Z)) (l_b: (@list Z)) (rp: Z) (bp: Z) (PreH1 : (rp = bp)) ,
  (UIntArray.seg bp 0 0 (@nil Z) )
  **  (UIntArray.seg bp 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
|--
  “ (rp = bp) ”
  &&  (UIntArray.seg rp 0 0 (@nil Z) )
  **  (UIntArray.seg rp 0 (Zlength (l_a)) (sublist (0) ((Zlength (l_a))) (l_b)) )
.

Definition mpn_add_n_which_implies_wit_7 := 
forall (l_a: (@list Z)) (rp: Z) (ap: Z) (i: Z) (PreH1 : (rp = ap)) ,
  (UIntArray.seg rp i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
|--
  “ (rp = ap) ”
  &&  (UIntArray.seg ap i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
.

Definition mpn_add_n_which_implies_wit_8 := 
forall (l_a: (@list Z)) (l_b: (@list Z)) (rp: Z) (bp: Z) (i: Z) (PreH1 : (rp = bp)) ,
  (UIntArray.seg rp i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
|--
  “ (rp = bp) ”
  &&  (UIntArray.seg bp i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
.

Definition mpn_add_n_which_implies_wit_9 := 
forall (l_a: (@list Z)) (rp: Z) (ap: Z) (i: Z) (PreH1 : (rp = ap)) ,
  (UIntArray.seg ap i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
|--
  “ (rp = ap) ”
  &&  (UIntArray.seg rp i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_a)) )
.

Definition mpn_add_n_which_implies_wit_10 := 
forall (l_a: (@list Z)) (l_b: (@list Z)) (rp: Z) (bp: Z) (i: Z) (PreH1 : (rp = bp)) ,
  (UIntArray.seg bp i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
|--
  “ (rp = bp) ”
  &&  (UIntArray.seg rp i (Zlength (l_a)) (sublist (i) ((Zlength (l_a))) (l_b)) )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_add_n_safety_wit_1_rp_eq_bp : mpn_add_n_safety_wit_1_rp_eq_bp.
Axiom proof_of_mpn_add_n_safety_wit_2_rp_eq_ap : mpn_add_n_safety_wit_2_rp_eq_ap.
Axiom proof_of_mpn_add_n_safety_wit_3_rp_eq_bp : mpn_add_n_safety_wit_3_rp_eq_bp.
Axiom proof_of_mpn_add_n_safety_wit_4_rp_eq_ap : mpn_add_n_safety_wit_4_rp_eq_ap.
Axiom proof_of_mpn_add_n_safety_wit_5_rp_eq_bp : mpn_add_n_safety_wit_5_rp_eq_bp.
Axiom proof_of_mpn_add_n_safety_wit_6_rp_eq_bp : mpn_add_n_safety_wit_6_rp_eq_bp.
Axiom proof_of_mpn_add_n_safety_wit_7_rp_eq_bp : mpn_add_n_safety_wit_7_rp_eq_bp.
Axiom proof_of_mpn_add_n_safety_wit_8_rp_eq_bp : mpn_add_n_safety_wit_8_rp_eq_bp.
Axiom proof_of_mpn_add_n_safety_wit_9_rp_eq_ap : mpn_add_n_safety_wit_9_rp_eq_ap.
Axiom proof_of_mpn_add_n_safety_wit_10_rp_eq_ap : mpn_add_n_safety_wit_10_rp_eq_ap.
Axiom proof_of_mpn_add_n_safety_wit_11_rp_eq_ap : mpn_add_n_safety_wit_11_rp_eq_ap.
Axiom proof_of_mpn_add_n_safety_wit_12_rp_eq_ap : mpn_add_n_safety_wit_12_rp_eq_ap.
Axiom proof_of_mpn_add_n_entail_wit_1_rp_eq_bp : mpn_add_n_entail_wit_1_rp_eq_bp.
Axiom proof_of_mpn_add_n_entail_wit_2_rp_eq_ap : mpn_add_n_entail_wit_2_rp_eq_ap.
Axiom proof_of_mpn_add_n_entail_wit_3_1_rp_eq_bp : mpn_add_n_entail_wit_3_1_rp_eq_bp.
Axiom proof_of_mpn_add_n_entail_wit_3_2_rp_eq_bp : mpn_add_n_entail_wit_3_2_rp_eq_bp.
Axiom proof_of_mpn_add_n_entail_wit_3_3_rp_eq_bp : mpn_add_n_entail_wit_3_3_rp_eq_bp.
Axiom proof_of_mpn_add_n_entail_wit_3_4_rp_eq_bp : mpn_add_n_entail_wit_3_4_rp_eq_bp.
Axiom proof_of_mpn_add_n_entail_wit_4_1_rp_eq_ap : mpn_add_n_entail_wit_4_1_rp_eq_ap.
Axiom proof_of_mpn_add_n_entail_wit_4_2_rp_eq_ap : mpn_add_n_entail_wit_4_2_rp_eq_ap.
Axiom proof_of_mpn_add_n_entail_wit_4_3_rp_eq_ap : mpn_add_n_entail_wit_4_3_rp_eq_ap.
Axiom proof_of_mpn_add_n_entail_wit_4_4_rp_eq_ap : mpn_add_n_entail_wit_4_4_rp_eq_ap.
Axiom proof_of_mpn_add_n_return_wit_1_rp_eq_bp : mpn_add_n_return_wit_1_rp_eq_bp.
Axiom proof_of_mpn_add_n_return_wit_2_rp_eq_ap : mpn_add_n_return_wit_2_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_1_rp_eq_ap : mpn_add_n_partial_solve_wit_1_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_2_rp_eq_bp : mpn_add_n_partial_solve_wit_2_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_3_rp_eq_ap_pure : mpn_add_n_partial_solve_wit_3_rp_eq_ap_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_3_rp_eq_ap : mpn_add_n_partial_solve_wit_3_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_4_rp_eq_bp_pure : mpn_add_n_partial_solve_wit_4_rp_eq_bp_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_4_rp_eq_bp : mpn_add_n_partial_solve_wit_4_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_5_rp_eq_ap_pure : mpn_add_n_partial_solve_wit_5_rp_eq_ap_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_5_rp_eq_ap : mpn_add_n_partial_solve_wit_5_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_6_rp_eq_bp_pure : mpn_add_n_partial_solve_wit_6_rp_eq_bp_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_6_rp_eq_bp : mpn_add_n_partial_solve_wit_6_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_7_rp_eq_ap_pure : mpn_add_n_partial_solve_wit_7_rp_eq_ap_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_7_rp_eq_ap : mpn_add_n_partial_solve_wit_7_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_8_rp_eq_bp_pure : mpn_add_n_partial_solve_wit_8_rp_eq_bp_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_8_rp_eq_bp : mpn_add_n_partial_solve_wit_8_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_9_rp_eq_bp : mpn_add_n_partial_solve_wit_9_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_10_rp_eq_ap : mpn_add_n_partial_solve_wit_10_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_11_rp_eq_bp : mpn_add_n_partial_solve_wit_11_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_12_rp_eq_ap : mpn_add_n_partial_solve_wit_12_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_13_rp_eq_ap_pure : mpn_add_n_partial_solve_wit_13_rp_eq_ap_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_13_rp_eq_ap : mpn_add_n_partial_solve_wit_13_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_14_rp_eq_ap_pure : mpn_add_n_partial_solve_wit_14_rp_eq_ap_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_14_rp_eq_ap : mpn_add_n_partial_solve_wit_14_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_15_rp_eq_ap_pure : mpn_add_n_partial_solve_wit_15_rp_eq_ap_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_15_rp_eq_ap : mpn_add_n_partial_solve_wit_15_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_16_rp_eq_ap_pure : mpn_add_n_partial_solve_wit_16_rp_eq_ap_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_16_rp_eq_ap : mpn_add_n_partial_solve_wit_16_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_17_rp_eq_bp_pure : mpn_add_n_partial_solve_wit_17_rp_eq_bp_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_17_rp_eq_bp : mpn_add_n_partial_solve_wit_17_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_18_rp_eq_bp_pure : mpn_add_n_partial_solve_wit_18_rp_eq_bp_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_18_rp_eq_bp : mpn_add_n_partial_solve_wit_18_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_19_rp_eq_bp_pure : mpn_add_n_partial_solve_wit_19_rp_eq_bp_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_19_rp_eq_bp : mpn_add_n_partial_solve_wit_19_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_20_rp_eq_bp_pure : mpn_add_n_partial_solve_wit_20_rp_eq_bp_pure.
Axiom proof_of_mpn_add_n_partial_solve_wit_20_rp_eq_bp : mpn_add_n_partial_solve_wit_20_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_21_rp_eq_bp : mpn_add_n_partial_solve_wit_21_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_22_rp_eq_bp : mpn_add_n_partial_solve_wit_22_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_23_rp_eq_bp : mpn_add_n_partial_solve_wit_23_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_24_rp_eq_bp : mpn_add_n_partial_solve_wit_24_rp_eq_bp.
Axiom proof_of_mpn_add_n_partial_solve_wit_25_rp_eq_ap : mpn_add_n_partial_solve_wit_25_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_26_rp_eq_ap : mpn_add_n_partial_solve_wit_26_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_27_rp_eq_ap : mpn_add_n_partial_solve_wit_27_rp_eq_ap.
Axiom proof_of_mpn_add_n_partial_solve_wit_28_rp_eq_ap : mpn_add_n_partial_solve_wit_28_rp_eq_ap.
Axiom proof_of_mpn_add_n_which_implies_wit_1 : mpn_add_n_which_implies_wit_1.
Axiom proof_of_mpn_add_n_which_implies_wit_2 : mpn_add_n_which_implies_wit_2.
Axiom proof_of_mpn_add_n_which_implies_wit_3 : mpn_add_n_which_implies_wit_3.
Axiom proof_of_mpn_add_n_which_implies_wit_4 : mpn_add_n_which_implies_wit_4.
Axiom proof_of_mpn_add_n_which_implies_wit_5 : mpn_add_n_which_implies_wit_5.
Axiom proof_of_mpn_add_n_which_implies_wit_6 : mpn_add_n_which_implies_wit_6.
Axiom proof_of_mpn_add_n_which_implies_wit_7 : mpn_add_n_which_implies_wit_7.
Axiom proof_of_mpn_add_n_which_implies_wit_8 : mpn_add_n_which_implies_wit_8.
Axiom proof_of_mpn_add_n_which_implies_wit_9 : mpn_add_n_which_implies_wit_9.
Axiom proof_of_mpn_add_n_which_implies_wit_10 : mpn_add_n_which_implies_wit_10.

End VC_Correct.
