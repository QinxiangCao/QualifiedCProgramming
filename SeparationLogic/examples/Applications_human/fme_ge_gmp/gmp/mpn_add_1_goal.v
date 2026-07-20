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

(*----- Function mpn_add_1 -----*)

Definition mpn_add_1_safety_wit_1_non_alias := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : (rp_pre <> ap_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (b_pre = b0_non_alias)) (PreH7 : (0 <= b0_non_alias)) (PreH8 : (b0_non_alias <= UINT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_1_safety_wit_2_rp_eq_ap := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (b_pre = b0_rp_eq_ap)) (PreH7 : (0 <= b0_rp_eq_ap)) (PreH8 : (b0_rp_eq_ap <= UINT_MAX)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_add_1_safety_wit_3_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) >= b0_non_alias)) (PreH2 : (0 <= b0_non_alias)) (PreH3 : (b0_non_alias <= UINT_MAX)) (PreH4 : (i = 0)) (PreH5 : (rp_pre <> ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH9 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
  **  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)))
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_safety_wit_4_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) < b0_non_alias)) (PreH2 : (0 <= b0_non_alias)) (PreH3 : (b0_non_alias <= UINT_MAX)) (PreH4 : (i = 0)) (PreH5 : (rp_pre <> ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH9 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
  **  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)))
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_safety_wit_5_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) >= b0_rp_eq_ap)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (0 <= b0_rp_eq_ap)) (PreH5 : (b0_rp_eq_ap <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_safety_wit_6_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) < b0_rp_eq_ap)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (0 <= b0_rp_eq_ap)) (PreH5 : (b0_rp_eq_ap <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_safety_wit_7_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l')) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH11 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH12 : (list_within_bound UINT_MOD l' )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l') ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_safety_wit_8_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l')) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH11 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH12 : (list_within_bound UINT_MOD l' )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l') ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b )) (32)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_safety_wit_9_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) >= b)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= b)) (PreH8 : (b <= 1)) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (n_pre > 0)) (PreH11 : ((Zlength (l')) = i)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH13 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH14 : (list_within_bound UINT_MOD l' )) (PreH15 : (list_within_bound UINT_MOD l )) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH18 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> 0)
  **  (UIntArray.seg rp_pre 0 i l' )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_safety_wit_10_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) < b)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= b)) (PreH8 : (b <= 1)) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (n_pre > 0)) (PreH11 : ((Zlength (l')) = i)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH13 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH14 : (list_within_bound UINT_MOD l' )) (PreH15 : (list_within_bound UINT_MOD l )) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH18 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)))
  **  ((( &( "b" ) )) # UInt  |-> 1)
  **  (UIntArray.seg rp_pre 0 i l' )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_add_1_entail_wit_1_rp_eq_ap := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (PreH1 : (rp_pre = rp_pre)) (PreH2 : (n_pre >= 0)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH5 : (list_within_bound UINT_MOD l )) (PreH6 : (rp_pre = ap_pre)) (PreH7 : (n_pre > 0)) (PreH8 : (b_pre = b0_rp_eq_ap)) (PreH9 : (0 <= b0_rp_eq_ap)) (PreH10 : (b0_rp_eq_ap <= UINT_MAX)) ,
  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg rp_pre 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
|--
  “ (0 <= b0_rp_eq_ap) ” 
  &&  “ (b0_rp_eq_ap <= UINT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "b" ) )) # UInt  |-> b0_rp_eq_ap)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg rp_pre 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
.

Definition mpn_add_1_entail_wit_2_non_alias := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : (rp_pre <> ap_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (b_pre = b0_non_alias)) (PreH7 : (0 <= b0_non_alias)) (PreH8 : (b0_non_alias <= UINT_MAX)) ,
  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= b0_non_alias) ” 
  &&  “ (b0_non_alias <= UINT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  ((( &( "b" ) )) # UInt  |-> b0_non_alias)
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_1_entail_wit_3_1_non_alias := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (val2: Z)  (val1: Z)  (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ ((val2 + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b0_non_alias )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_non_alias )) ” 
  &&  “ (list_within_bound UINT_MOD (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition mpn_add_1_entail_wit_3_1_non_alias_split_goal_1 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  (((list_to_Z (UINT_MOD) ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_non_alias ))
.

Definition mpn_add_1_entail_wit_3_1_non_alias_split_goal_2 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  (list_within_bound UINT_MOD (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
.

Definition mpn_add_1_entail_wit_3_1_non_alias_split_goal_3 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  ((Zlength ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_add_1_entail_wit_3_2_non_alias := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  (UIntArray.seg rp_pre 0 (i + 1 ) (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (val2: Z)  (val1: Z)  (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ ((val2 + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b0_non_alias )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  TT && emp 
|--
  “ (((list_to_Z (UINT_MOD) ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_non_alias )) ” 
  &&  “ (list_within_bound UINT_MOD (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition mpn_add_1_entail_wit_3_2_non_alias_split_goal_1 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  (((list_to_Z (UINT_MOD) ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_non_alias ))
.

Definition mpn_add_1_entail_wit_3_2_non_alias_split_goal_2 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  (list_within_bound UINT_MOD (app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))) )
.

Definition mpn_add_1_entail_wit_3_2_non_alias_split_goal_3 := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l'_2)) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH11 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH12 : (list_within_bound UINT_MOD l'_2 )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_non_alias ))) ,
  ((Zlength ((app (l'_2) ((cons ((unsigned_last_nbits (((Znth i l 0) + b )) (32))) ((@nil Z))))))) = (i + 1 ))
.

Definition mpn_add_1_entail_wit_4_1_rp_eq_ap := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) >= b)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= b)) (PreH8 : (b <= 1)) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (n_pre > 0)) (PreH11 : ((Zlength (l'_2)) = i)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH14 : (list_within_bound UINT_MOD l'_2 )) (PreH15 : (list_within_bound UINT_MOD l )) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH18 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  (UIntArray.seg rp_pre 0 i l'_2 )
|--
  EX (val2: Z)  (val1: Z)  (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ ((val2 + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l)) (sublist ((i + 1 )) ((Zlength (l))) (l)) )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) >= b)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= b)) (PreH8 : (b <= 1)) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (n_pre > 0)) (PreH11 : ((Zlength (l'_2)) = i)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH14 : (list_within_bound UINT_MOD l'_2 )) (PreH15 : (list_within_bound UINT_MOD l )) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH18 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  (UIntArray.seg rp_pre 0 i l'_2 )
|--
  EX (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l')) + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l)) (sublist ((i + 1 )) ((Zlength (l))) (l)) )
).

Definition mpn_add_1_entail_wit_4_2_rp_eq_ap := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) < b)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= b)) (PreH8 : (b <= 1)) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (n_pre > 0)) (PreH11 : ((Zlength (l'_2)) = i)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH14 : (list_within_bound UINT_MOD l'_2 )) (PreH15 : (list_within_bound UINT_MOD l )) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH18 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  (UIntArray.seg rp_pre 0 i l'_2 )
|--
  EX (val2: Z)  (val1: Z)  (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ ((val2 + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l)) (sublist ((i + 1 )) ((Zlength (l))) (l)) )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2_2: Z) (val1_2: Z) (l'_2: (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) < b)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= b)) (PreH8 : (b <= 1)) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (n_pre > 0)) (PreH11 : ((Zlength (l'_2)) = i)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1_2)) (PreH13 : ((list_to_Z (UINT_MOD) (l'_2)) = val2_2)) (PreH14 : (list_within_bound UINT_MOD l'_2 )) (PreH15 : (list_within_bound UINT_MOD l )) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH18 : ((val2_2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1_2 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  (UIntArray.seg rp_pre 0 i l'_2 )
|--
  EX (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l')) + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l)) (sublist ((i + 1 )) ((Zlength (l))) (l)) )
).

Definition mpn_add_1_entail_wit_5_1_non_alias := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) >= b0_non_alias)) (PreH2 : (0 <= b0_non_alias)) (PreH3 : (b0_non_alias <= UINT_MAX)) (PreH4 : (i = 0)) (PreH5 : (rp_pre <> ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH9 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
  **  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)))
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (val2: Z)  (val1: Z)  (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ ((val2 + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b0_non_alias )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) >= 0)) (PreH3 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) >= b0_non_alias)) (PreH4 : (0 <= b0_non_alias)) (PreH5 : (b0_non_alias <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)))
|--
  EX (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l')) + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_non_alias )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
).

Definition mpn_add_1_entail_wit_5_2_non_alias := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) < b0_non_alias)) (PreH2 : (0 <= b0_non_alias)) (PreH3 : (b0_non_alias <= UINT_MAX)) (PreH4 : (i = 0)) (PreH5 : (rp_pre <> ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH9 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.undef_seg rp_pre (0 + 1 ) n_pre )
  **  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)))
  **  (UIntArray.full ap_pre n_pre l )
|--
  EX (val2: Z)  (val1: Z)  (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ ((val2 + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b0_non_alias )) ”
  &&  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) >= 0)) (PreH3 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) < b0_non_alias)) (PreH4 : (0 <= b0_non_alias)) (PreH5 : (b0_non_alias <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)))
|--
  EX (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l')) + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_non_alias )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
).

Definition mpn_add_1_entail_wit_6_1_rp_eq_ap := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) >= b0_rp_eq_ap)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (0 <= b0_rp_eq_ap)) (PreH5 : (b0_rp_eq_ap <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  EX (val2: Z)  (val1: Z)  (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ ((val2 + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l)) (sublist ((i + 1 )) ((Zlength (l))) (l)) )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) >= b0_rp_eq_ap)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (0 <= b0_rp_eq_ap)) (PreH5 : (b0_rp_eq_ap <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  EX (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l')) + (0 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l)) (sublist ((i + 1 )) ((Zlength (l))) (l)) )
).

Definition mpn_add_1_entail_wit_6_2_rp_eq_ap := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) < b0_rp_eq_ap)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (0 <= b0_rp_eq_ap)) (PreH5 : (b0_rp_eq_ap <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  EX (val2: Z)  (val1: Z)  (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ ((val2 + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = (val1 + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l)) (sublist ((i + 1 )) ((Zlength (l))) (l)) )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) < b0_rp_eq_ap)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (0 <= b0_rp_eq_ap)) (PreH5 : (b0_rp_eq_ap <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32))) ((sublist (i) ((Zlength (l))) (l)))) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  EX (l': (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = (i + 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l')) + (1 * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l)))) + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l' )
  **  (UIntArray.seg rp_pre (i + 1 ) (Zlength (l)) (sublist ((i + 1 )) ((Zlength (l))) (l)) )
).

Definition mpn_add_1_return_wit_1_non_alias := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : (rp_pre <> ap_pre)) (PreH7 : (n_pre > 0)) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : (list_within_bound UINT_MOD l )) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH15 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  EX (val': Z) ,
  “ ((val' + (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_non_alias + b0_non_alias )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_non_alias n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : (rp_pre <> ap_pre)) (PreH7 : (n_pre > 0)) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : (list_within_bound UINT_MOD l )) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH15 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l' )
|--
  EX (val': Z) ,
  “ ((val' + (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_non_alias + b0_non_alias )) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_non_alias n_pre )
  **  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
).

Definition mpn_add_1_return_wit_2_rp_eq_ap := 
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : (rp_pre = ap_pre)) (PreH7 : (n_pre > 0)) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : (list_within_bound UINT_MOD l )) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH15 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre 0 i l' )
  **  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
|--
  EX (val': Z) ,
  “ ((val' + (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_rp_eq_ap + b0_rp_eq_ap )) ” 
  &&  “ (rp_pre = ap_pre) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
) \/
(
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : (rp_pre = ap_pre)) (PreH7 : (n_pre > 0)) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : (list_within_bound UINT_MOD l )) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH15 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre 0 i l' )
  **  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
|--
  EX (val': Z) ,
  “ ((val' + (b * (Z.pow (UINT_MOD) (n_pre)) ) ) = (val_rp_eq_ap + b0_rp_eq_ap )) ” 
  &&  “ (rp_pre = ap_pre) ”
  &&  (mpd_store_Z UINT_MOD rp_pre val' n_pre )
).

Definition mpn_add_1_partial_solve_wit_1_rp_eq_ap := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (b_pre = b0_rp_eq_ap)) (PreH4 : (0 <= b0_rp_eq_ap)) (PreH5 : (b0_rp_eq_ap <= UINT_MAX)) ,
  (mpd_store_Z UINT_MOD ap_pre val_rp_eq_ap n_pre )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (b_pre = b0_rp_eq_ap) ” 
  &&  “ (0 <= b0_rp_eq_ap) ” 
  &&  “ (b0_rp_eq_ap <= UINT_MAX) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_rp_eq_ap n_pre )
.

Definition mpn_add_1_partial_solve_wit_2_non_alias := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (PreH1 : (rp_pre <> ap_pre)) (PreH2 : (n_pre > 0)) (PreH3 : (b_pre = b0_non_alias)) (PreH4 : (0 <= b0_non_alias)) (PreH5 : (b0_non_alias <= UINT_MAX)) ,
  (mpd_store_Z UINT_MOD ap_pre val_non_alias n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (b_pre = b0_non_alias) ” 
  &&  “ (0 <= b0_non_alias) ” 
  &&  “ (b0_non_alias <= UINT_MAX) ”
  &&  (mpd_store_Z UINT_MOD ap_pre val_non_alias n_pre )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_1_partial_solve_wit_3_rp_eq_ap_pure := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (b_pre = b0_rp_eq_ap)) (PreH7 : (0 <= b0_rp_eq_ap)) (PreH8 : (b0_rp_eq_ap <= UINT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.full ap_pre n_pre l )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
|--
  “ (n_pre >= 0) ”
.

Definition mpn_add_1_partial_solve_wit_3_rp_eq_ap_aux := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre > 0)) (PreH6 : (b_pre = b0_rp_eq_ap)) (PreH7 : (0 <= b0_rp_eq_ap)) (PreH8 : (b0_rp_eq_ap <= UINT_MAX)) ,
  (UIntArray.full ap_pre n_pre l )
|--
  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (b_pre = b0_rp_eq_ap) ” 
  &&  “ (0 <= b0_rp_eq_ap) ” 
  &&  “ (b0_rp_eq_ap <= UINT_MAX) ”
  &&  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_add_1_partial_solve_wit_3_rp_eq_ap := mpn_add_1_partial_solve_wit_3_rp_eq_ap_pure -> mpn_add_1_partial_solve_wit_3_rp_eq_ap_aux.

Definition mpn_add_1_partial_solve_wit_4_rp_eq_ap_pure := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (rp_pre = ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : (b_pre = b0_rp_eq_ap)) (PreH8 : (0 <= b0_rp_eq_ap)) (PreH9 : (b0_rp_eq_ap <= UINT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg ap_pre 0 0 (@nil Z) )
  **  (UIntArray.seg ap_pre 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "b" ) )) # UInt  |-> b_pre)
|--
  “ (rp_pre = rp_pre) ”
.

Definition mpn_add_1_partial_solve_wit_4_rp_eq_ap_aux := 
forall (b_pre: Z) (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH4 : (list_within_bound UINT_MOD l )) (PreH5 : (rp_pre = ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : (b_pre = b0_rp_eq_ap)) (PreH8 : (0 <= b0_rp_eq_ap)) (PreH9 : (b0_rp_eq_ap <= UINT_MAX)) ,
  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg ap_pre 0 0 (@nil Z) )
  **  (UIntArray.seg ap_pre 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
|--
  “ (rp_pre = rp_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (b_pre = b0_rp_eq_ap) ” 
  &&  “ (0 <= b0_rp_eq_ap) ” 
  &&  “ (b0_rp_eq_ap <= UINT_MAX) ”
  &&  ((( &( "ap" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg rp_pre 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
.

Definition mpn_add_1_partial_solve_wit_4_rp_eq_ap := mpn_add_1_partial_solve_wit_4_rp_eq_ap_pure -> mpn_add_1_partial_solve_wit_4_rp_eq_ap_aux.

Definition mpn_add_1_partial_solve_wit_5_rp_eq_ap_pure := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : (0 <= b0_rp_eq_ap)) (PreH2 : (b0_rp_eq_ap <= UINT_MAX)) (PreH3 : (i = 0)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre > 0)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH8 : (list_within_bound UINT_MOD l )) ,
  ((( &( "b" ) )) # UInt  |-> b0_rp_eq_ap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg rp_pre 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
|--
  “ (rp_pre = ap_pre) ”
.

Definition mpn_add_1_partial_solve_wit_5_rp_eq_ap_aux := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : (0 <= b0_rp_eq_ap)) (PreH2 : (b0_rp_eq_ap <= UINT_MAX)) (PreH3 : (i = 0)) (PreH4 : (rp_pre = ap_pre)) (PreH5 : (n_pre > 0)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH8 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre 0 0 (@nil Z) )
  **  (UIntArray.seg rp_pre 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (0 <= b0_rp_eq_ap) ” 
  &&  “ (b0_rp_eq_ap <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
.

Definition mpn_add_1_partial_solve_wit_5_rp_eq_ap := mpn_add_1_partial_solve_wit_5_rp_eq_ap_pure -> mpn_add_1_partial_solve_wit_5_rp_eq_ap_aux.

Definition mpn_add_1_partial_solve_wit_6_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (i: Z) (PreH1 : (0 <= b0_non_alias)) (PreH2 : (b0_non_alias <= UINT_MAX)) (PreH3 : (i = 0)) (PreH4 : (rp_pre <> ap_pre)) (PreH5 : (n_pre > 0)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH8 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ (0 <= b0_non_alias) ” 
  &&  “ (b0_non_alias <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((ap_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
.

Definition mpn_add_1_partial_solve_wit_7_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (0 <= b0_rp_eq_ap)) (PreH3 : (b0_rp_eq_ap <= UINT_MAX)) (PreH4 : (i = 0)) (PreH5 : (rp_pre = ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH9 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (0 <= b0_rp_eq_ap) ” 
  &&  “ (b0_rp_eq_ap <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((ap_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0))
  **  (UIntArray.missing_i ap_pre i i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
.

Definition mpn_add_1_partial_solve_wit_8_rp_eq_ap_pure := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (0 <= b0_rp_eq_ap)) (PreH3 : (b0_rp_eq_ap <= UINT_MAX)) (PreH4 : (i = 0)) (PreH5 : (rp_pre = ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH9 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> b0_rp_eq_ap)
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  “ (rp_pre = ap_pre) ”
.

Definition mpn_add_1_partial_solve_wit_8_rp_eq_ap_aux := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (0 <= b0_rp_eq_ap)) (PreH3 : (b0_rp_eq_ap <= UINT_MAX)) (PreH4 : (i = 0)) (PreH5 : (rp_pre = ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH9 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (0 <= b0_rp_eq_ap) ” 
  &&  “ (b0_rp_eq_ap <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
.

Definition mpn_add_1_partial_solve_wit_8_rp_eq_ap := mpn_add_1_partial_solve_wit_8_rp_eq_ap_pure -> mpn_add_1_partial_solve_wit_8_rp_eq_ap_aux.

Definition mpn_add_1_partial_solve_wit_9_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) >= b0_non_alias)) (PreH2 : (0 <= b0_non_alias)) (PreH3 : (b0_non_alias <= UINT_MAX)) (PreH4 : (i = 0)) (PreH5 : (rp_pre <> ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH9 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) >= b0_non_alias) ” 
  &&  “ (0 <= b0_non_alias) ” 
  &&  “ (b0_non_alias <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i rp_pre i 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_add_1_partial_solve_wit_10_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) < b0_non_alias)) (PreH2 : (0 <= b0_non_alias)) (PreH3 : (b0_non_alias <= UINT_MAX)) (PreH4 : (i = 0)) (PreH5 : (rp_pre <> ap_pre)) (PreH6 : (n_pre > 0)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH9 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.undef_full rp_pre n_pre )
|--
  “ ((unsigned_last_nbits (((Znth i l 0) + b0_non_alias )) (32)) < b0_non_alias) ” 
  &&  “ (0 <= b0_non_alias) ” 
  &&  “ (b0_non_alias <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i rp_pre i 0 n_pre )
  **  (UIntArray.full ap_pre n_pre l )
.

Definition mpn_add_1_partial_solve_wit_11_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) >= b0_rp_eq_ap)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (0 <= b0_rp_eq_ap)) (PreH5 : (b0_rp_eq_ap <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) >= b0_rp_eq_ap) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (0 <= b0_rp_eq_ap) ” 
  &&  “ (b0_rp_eq_ap <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
.

Definition mpn_add_1_partial_solve_wit_12_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) < b0_rp_eq_ap)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (0 <= b0_rp_eq_ap)) (PreH5 : (b0_rp_eq_ap <= UINT_MAX)) (PreH6 : (i = 0)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH11 : (list_within_bound UINT_MOD l )) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
|--
  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b0_rp_eq_ap )) (32)) < b0_rp_eq_ap) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (0 <= b0_rp_eq_ap) ” 
  &&  “ (b0_rp_eq_ap <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 0 (@nil Z) )
.

Definition mpn_add_1_partial_solve_wit_13_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l')) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH11 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH12 : (list_within_bound UINT_MOD l' )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) >= b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l' )
.

Definition mpn_add_1_partial_solve_wit_14_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre <> ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l')) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH11 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH12 : (list_within_bound UINT_MOD l' )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH16 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ ((unsigned_last_nbits (((Znth i l 0) + b )) (32)) < b) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre (i + 1 ) n_pre )
  **  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l' )
.

Definition mpn_add_1_partial_solve_wit_15_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) >= b)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= b)) (PreH8 : (b <= 1)) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (n_pre > 0)) (PreH11 : ((Zlength (l')) = i)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH13 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH14 : (list_within_bound UINT_MOD l' )) (PreH15 : (list_within_bound UINT_MOD l )) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH18 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 i l' )
|--
  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) >= b) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 i l' )
.

Definition mpn_add_1_partial_solve_wit_16_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) < b)) (PreH2 : (rp_pre = ap_pre)) (PreH3 : (rp_pre = ap_pre)) (PreH4 : (i < n_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= b)) (PreH8 : (b <= 1)) (PreH9 : (rp_pre = ap_pre)) (PreH10 : (n_pre > 0)) (PreH11 : ((Zlength (l')) = i)) (PreH12 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH13 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH14 : (list_within_bound UINT_MOD l' )) (PreH15 : (list_within_bound UINT_MOD l )) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH18 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 i l' )
|--
  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)) < b) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 i l' )
.

Definition mpn_add_1_partial_solve_wit_17_rp_eq_ap_pure := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l')) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH11 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH12 : (list_within_bound UINT_MOD l' )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH16 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  ((( &( "r" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0) + b )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "b" ) )) # UInt  |-> b)
  **  (UIntArray.seg rp_pre 0 i l' )
|--
  “ (rp_pre = ap_pre) ”
.

Definition mpn_add_1_partial_solve_wit_17_rp_eq_ap_aux := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l')) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH11 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH12 : (list_within_bound UINT_MOD l' )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH16 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 i l' )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 i l' )
.

Definition mpn_add_1_partial_solve_wit_17_rp_eq_ap := mpn_add_1_partial_solve_wit_17_rp_eq_ap_pure -> mpn_add_1_partial_solve_wit_17_rp_eq_ap_aux.

Definition mpn_add_1_partial_solve_wit_18_non_alias := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_non_alias: Z) (val_non_alias: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : (rp_pre <> ap_pre)) (PreH7 : (n_pre > 0)) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : (list_within_bound UINT_MOD l )) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l)) = val_non_alias)) (PreH15 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias ))) ,
  (UIntArray.full ap_pre n_pre l )
  **  (UIntArray.seg rp_pre 0 i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ (rp_pre <> ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_non_alias )) ”
  &&  (((ap_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l 0))
  **  (UIntArray.missing_i ap_pre i 0 n_pre l )
  **  (UIntArray.seg rp_pre 0 i l' )
  **  (UIntArray.undef_seg rp_pre i n_pre )
.

Definition mpn_add_1_partial_solve_wit_19_rp_eq_ap := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (rp_pre = ap_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (0 <= b)) (PreH6 : (b <= 1)) (PreH7 : (rp_pre = ap_pre)) (PreH8 : (n_pre > 0)) (PreH9 : ((Zlength (l')) = i)) (PreH10 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH11 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH12 : (list_within_bound UINT_MOD l' )) (PreH13 : (list_within_bound UINT_MOD l )) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH16 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 i l' )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap )) ”
  &&  (((ap_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist (i) ((Zlength (l))) (l)) 0))
  **  (UIntArray.missing_i ap_pre i i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 i l' )
.

Definition mpn_add_1_partial_solve_wit_20_rp_eq_ap_pure := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : (rp_pre = ap_pre)) (PreH7 : (n_pre > 0)) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : (list_within_bound UINT_MOD l )) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH15 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "b" ) )) # UInt  |-> b)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "ap" ) )) # Ptr  |-> ap_pre)
  **  (UIntArray.seg rp_pre 0 i l' )
  **  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
|--
  “ (rp_pre = ap_pre) ”
.

Definition mpn_add_1_partial_solve_wit_20_rp_eq_ap_aux := 
forall (n_pre: Z) (ap_pre: Z) (rp_pre: Z) (b0_rp_eq_ap: Z) (val_rp_eq_ap: Z) (l: (@list Z)) (val2: Z) (val1: Z) (l': (@list Z)) (b: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= b)) (PreH5 : (b <= 1)) (PreH6 : (rp_pre = ap_pre)) (PreH7 : (n_pre > 0)) (PreH8 : ((Zlength (l')) = i)) (PreH9 : ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1)) (PreH10 : ((list_to_Z (UINT_MOD) (l')) = val2)) (PreH11 : (list_within_bound UINT_MOD l' )) (PreH12 : (list_within_bound UINT_MOD l )) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap)) (PreH15 : ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap ))) ,
  (UIntArray.seg rp_pre 0 i l' )
  **  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
|--
  “ (rp_pre = ap_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= b) ” 
  &&  “ (b <= 1) ” 
  &&  “ (rp_pre = ap_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l')) = i) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l)))) = val1) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l')) = val2) ” 
  &&  “ (list_within_bound UINT_MOD l' ) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ ((val2 + (b * (Z.pow (UINT_MOD) (i)) ) ) = (val1 + b0_rp_eq_ap )) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
  **  (UIntArray.seg rp_pre 0 i l' )
.

Definition mpn_add_1_partial_solve_wit_20_rp_eq_ap := mpn_add_1_partial_solve_wit_20_rp_eq_ap_pure -> mpn_add_1_partial_solve_wit_20_rp_eq_ap_aux.

Definition mpn_add_1_which_implies_wit_1 := 
(
forall (val_rp_eq_ap: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val_rp_eq_ap n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
) \/
(
forall (val_rp_eq_ap: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val_rp_eq_ap n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_rp_eq_ap) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
).

Definition mpn_add_1_which_implies_wit_2 := 
(
forall (val_non_alias: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val_non_alias n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
) \/
(
forall (val_non_alias: Z) (n: Z) (ap: Z) ,
  (mpd_store_Z UINT_MOD ap val_non_alias n )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = val_non_alias) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
  &&  (UIntArray.full ap n l )
).

Definition mpn_add_1_which_implies_wit_3 := 
(
forall (l: (@list Z)) (n: Z) (ap: Z) (PreH1 : (n >= 0)) ,
  (UIntArray.full ap n l )
|--
  “ (n >= 0) ”
  &&  (UIntArray.seg ap 0 0 (@nil Z) )
  **  (UIntArray.seg ap 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
) \/
(
forall (l: (@list Z)) (n: Z) (ap: Z) (PreH1 : (n >= 0)) ,
  (UIntArray.full ap n l )
|--
  (UIntArray.seg ap 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
).

Definition mpn_add_1_which_implies_wit_3_split_goal_spatial := 
forall (l: (@list Z)) (n: Z) (ap: Z) (PreH1 : (n >= 0)) ,
  (UIntArray.full ap n l )
|--
  (UIntArray.seg ap 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
.

Definition mpn_add_1_which_implies_wit_4 := 
forall (l: (@list Z)) (rp: Z) (ap: Z) (PreH1 : (rp = ap)) ,
  (UIntArray.seg ap 0 0 (@nil Z) )
  **  (UIntArray.seg ap 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
|--
  “ (rp = ap) ”
  &&  (UIntArray.seg rp 0 0 (@nil Z) )
  **  (UIntArray.seg rp 0 (Zlength (l)) (sublist (0) ((Zlength (l))) (l)) )
.

Definition mpn_add_1_which_implies_wit_5 := 
forall (ap_pre: Z) (rp_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (rp_pre = ap_pre)) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
|--
  “ (rp_pre = ap_pre) ”
  &&  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
.

Definition mpn_add_1_which_implies_wit_6 := 
forall (ap_pre: Z) (rp_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (rp_pre = ap_pre)) ,
  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
|--
  “ (rp_pre = ap_pre) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
.

Definition mpn_add_1_which_implies_wit_7 := 
forall (ap_pre: Z) (rp_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (rp_pre = ap_pre)) ,
  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
|--
  “ (rp_pre = ap_pre) ”
  &&  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
.

Definition mpn_add_1_which_implies_wit_8 := 
forall (ap_pre: Z) (rp_pre: Z) (l: (@list Z)) (i: Z) (PreH1 : (rp_pre = ap_pre)) ,
  (UIntArray.seg rp_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
|--
  “ (rp_pre = ap_pre) ”
  &&  (UIntArray.seg ap_pre i (Zlength (l)) (sublist (i) ((Zlength (l))) (l)) )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_add_1_safety_wit_1_non_alias : mpn_add_1_safety_wit_1_non_alias.
Axiom proof_of_mpn_add_1_safety_wit_2_rp_eq_ap : mpn_add_1_safety_wit_2_rp_eq_ap.
Axiom proof_of_mpn_add_1_safety_wit_3_non_alias : mpn_add_1_safety_wit_3_non_alias.
Axiom proof_of_mpn_add_1_safety_wit_4_non_alias : mpn_add_1_safety_wit_4_non_alias.
Axiom proof_of_mpn_add_1_safety_wit_5_rp_eq_ap : mpn_add_1_safety_wit_5_rp_eq_ap.
Axiom proof_of_mpn_add_1_safety_wit_6_rp_eq_ap : mpn_add_1_safety_wit_6_rp_eq_ap.
Axiom proof_of_mpn_add_1_safety_wit_7_non_alias : mpn_add_1_safety_wit_7_non_alias.
Axiom proof_of_mpn_add_1_safety_wit_8_non_alias : mpn_add_1_safety_wit_8_non_alias.
Axiom proof_of_mpn_add_1_safety_wit_9_rp_eq_ap : mpn_add_1_safety_wit_9_rp_eq_ap.
Axiom proof_of_mpn_add_1_safety_wit_10_rp_eq_ap : mpn_add_1_safety_wit_10_rp_eq_ap.
Axiom proof_of_mpn_add_1_entail_wit_1_rp_eq_ap : mpn_add_1_entail_wit_1_rp_eq_ap.
Axiom proof_of_mpn_add_1_entail_wit_2_non_alias : mpn_add_1_entail_wit_2_non_alias.
Axiom proof_of_mpn_add_1_entail_wit_3_1_non_alias : mpn_add_1_entail_wit_3_1_non_alias.
Axiom proof_of_mpn_add_1_entail_wit_3_2_non_alias : mpn_add_1_entail_wit_3_2_non_alias.
Axiom proof_of_mpn_add_1_entail_wit_4_1_rp_eq_ap : mpn_add_1_entail_wit_4_1_rp_eq_ap.
Axiom proof_of_mpn_add_1_entail_wit_4_2_rp_eq_ap : mpn_add_1_entail_wit_4_2_rp_eq_ap.
Axiom proof_of_mpn_add_1_entail_wit_5_1_non_alias : mpn_add_1_entail_wit_5_1_non_alias.
Axiom proof_of_mpn_add_1_entail_wit_5_2_non_alias : mpn_add_1_entail_wit_5_2_non_alias.
Axiom proof_of_mpn_add_1_entail_wit_6_1_rp_eq_ap : mpn_add_1_entail_wit_6_1_rp_eq_ap.
Axiom proof_of_mpn_add_1_entail_wit_6_2_rp_eq_ap : mpn_add_1_entail_wit_6_2_rp_eq_ap.
Axiom proof_of_mpn_add_1_return_wit_1_non_alias : mpn_add_1_return_wit_1_non_alias.
Axiom proof_of_mpn_add_1_return_wit_2_rp_eq_ap : mpn_add_1_return_wit_2_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_1_rp_eq_ap : mpn_add_1_partial_solve_wit_1_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_2_non_alias : mpn_add_1_partial_solve_wit_2_non_alias.
Axiom proof_of_mpn_add_1_partial_solve_wit_3_rp_eq_ap_pure : mpn_add_1_partial_solve_wit_3_rp_eq_ap_pure.
Axiom proof_of_mpn_add_1_partial_solve_wit_3_rp_eq_ap : mpn_add_1_partial_solve_wit_3_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_4_rp_eq_ap_pure : mpn_add_1_partial_solve_wit_4_rp_eq_ap_pure.
Axiom proof_of_mpn_add_1_partial_solve_wit_4_rp_eq_ap : mpn_add_1_partial_solve_wit_4_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_5_rp_eq_ap_pure : mpn_add_1_partial_solve_wit_5_rp_eq_ap_pure.
Axiom proof_of_mpn_add_1_partial_solve_wit_5_rp_eq_ap : mpn_add_1_partial_solve_wit_5_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_6_non_alias : mpn_add_1_partial_solve_wit_6_non_alias.
Axiom proof_of_mpn_add_1_partial_solve_wit_7_rp_eq_ap : mpn_add_1_partial_solve_wit_7_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_8_rp_eq_ap_pure : mpn_add_1_partial_solve_wit_8_rp_eq_ap_pure.
Axiom proof_of_mpn_add_1_partial_solve_wit_8_rp_eq_ap : mpn_add_1_partial_solve_wit_8_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_9_non_alias : mpn_add_1_partial_solve_wit_9_non_alias.
Axiom proof_of_mpn_add_1_partial_solve_wit_10_non_alias : mpn_add_1_partial_solve_wit_10_non_alias.
Axiom proof_of_mpn_add_1_partial_solve_wit_11_rp_eq_ap : mpn_add_1_partial_solve_wit_11_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_12_rp_eq_ap : mpn_add_1_partial_solve_wit_12_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_13_non_alias : mpn_add_1_partial_solve_wit_13_non_alias.
Axiom proof_of_mpn_add_1_partial_solve_wit_14_non_alias : mpn_add_1_partial_solve_wit_14_non_alias.
Axiom proof_of_mpn_add_1_partial_solve_wit_15_rp_eq_ap : mpn_add_1_partial_solve_wit_15_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_16_rp_eq_ap : mpn_add_1_partial_solve_wit_16_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_17_rp_eq_ap_pure : mpn_add_1_partial_solve_wit_17_rp_eq_ap_pure.
Axiom proof_of_mpn_add_1_partial_solve_wit_17_rp_eq_ap : mpn_add_1_partial_solve_wit_17_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_18_non_alias : mpn_add_1_partial_solve_wit_18_non_alias.
Axiom proof_of_mpn_add_1_partial_solve_wit_19_rp_eq_ap : mpn_add_1_partial_solve_wit_19_rp_eq_ap.
Axiom proof_of_mpn_add_1_partial_solve_wit_20_rp_eq_ap_pure : mpn_add_1_partial_solve_wit_20_rp_eq_ap_pure.
Axiom proof_of_mpn_add_1_partial_solve_wit_20_rp_eq_ap : mpn_add_1_partial_solve_wit_20_rp_eq_ap.
Axiom proof_of_mpn_add_1_which_implies_wit_1 : mpn_add_1_which_implies_wit_1.
Axiom proof_of_mpn_add_1_which_implies_wit_2 : mpn_add_1_which_implies_wit_2.
Axiom proof_of_mpn_add_1_which_implies_wit_3 : mpn_add_1_which_implies_wit_3.
Axiom proof_of_mpn_add_1_which_implies_wit_4 : mpn_add_1_which_implies_wit_4.
Axiom proof_of_mpn_add_1_which_implies_wit_5 : mpn_add_1_which_implies_wit_5.
Axiom proof_of_mpn_add_1_which_implies_wit_6 : mpn_add_1_which_implies_wit_6.
Axiom proof_of_mpn_add_1_which_implies_wit_7 : mpn_add_1_which_implies_wit_7.
Axiom proof_of_mpn_add_1_which_implies_wit_8 : mpn_add_1_which_implies_wit_8.

End VC_Correct.
