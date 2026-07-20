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

(*----- Function mpn_submul_1 -----*)

Definition mpn_submul_1_safety_wit_1 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l_rp)) = n_pre)) (PreH6 : ((Zlength (l_up)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (list_within_bound UINT_MOD l_up )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "cl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  (UIntArray.full rp_pre n_pre l_rp )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_submul_1_safety_wit_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l_rp)) = n_pre)) (PreH6 : ((Zlength (l_up)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (list_within_bound UINT_MOD l_up )) ,
  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "cl" ) )) # UInt  |->_)
  **  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  (UIntArray.full rp_pre n_pre l_rp )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_submul_1_safety_wit_3 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> ((0 + hpl ) + 0 ))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_submul_1_safety_wit_4 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> ((0 + hpl ) + 0 ))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_submul_1_safety_wit_5 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (unsigned_last_nbits (((0 + hpl ) + 1 )) (32)))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_submul_1_safety_wit_6 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (unsigned_last_nbits (((0 + hpl ) + 1 )) (32)))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_submul_1_safety_wit_7 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> ((unsigned_last_nbits ((1 + hpl )) (32)) + 0 ))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_submul_1_safety_wit_8 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> ((unsigned_last_nbits ((1 + hpl )) (32)) + 0 ))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_submul_1_safety_wit_9 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((1 + hpl )) (32)) + 1 )) (32)))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_submul_1_safety_wit_10 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> (unsigned_last_nbits (((unsigned_last_nbits ((1 + hpl )) (32)) + 1 )) (32)))
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_submul_1_entail_wit_1 := 
(
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l_rp)) = n_pre)) (PreH6 : ((Zlength (l_up)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (list_within_bound UINT_MOD l_up )) ,
  (UIntArray.full rp_pre n_pre l_rp )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = 0) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_up)))) * vl_pre ) )) ”
  &&  (UIntArray.seg rp_pre 0 0 l_done )
  **  (UIntArray.seg rp_pre 0 n_pre (sublist (0) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
) \/
(
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l_rp)) = n_pre)) (PreH6 : ((Zlength (l_up)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (list_within_bound UINT_MOD l_up )) ,
  (UIntArray.full rp_pre n_pre l_rp )
|--
  “ (((list_to_Z (UINT_MOD) ((@nil Z))) - (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_up)))) * vl_pre ) )) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (UIntArray.seg rp_pre 0 n_pre (sublist (0) (n_pre) (l_rp)) )
).

Definition mpn_submul_1_entail_wit_1_split_goal_1 := 
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l_rp)) = n_pre)) (PreH6 : ((Zlength (l_up)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (list_within_bound UINT_MOD l_up )) ,
  (UIntArray.full rp_pre n_pre l_rp )
|--
  “ (((list_to_Z (UINT_MOD) ((@nil Z))) - (0 * (Z.pow (UINT_MOD) (0)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (0) (l_up)))) * vl_pre ) )) ”
.

Definition mpn_submul_1_entail_wit_1_split_goal_2 := 
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l_rp)) = n_pre)) (PreH6 : ((Zlength (l_up)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (list_within_bound UINT_MOD l_up )) ,
  (UIntArray.full rp_pre n_pre l_rp )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_submul_1_entail_wit_1_split_goal_3 := 
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l_rp)) = n_pre)) (PreH6 : ((Zlength (l_up)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (list_within_bound UINT_MOD l_up )) ,
  (UIntArray.full rp_pre n_pre l_rp )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition mpn_submul_1_entail_wit_1_split_goal_spatial := 
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : ((Zlength (l_rp)) = n_pre)) (PreH6 : ((Zlength (l_up)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_rp )) (PreH8 : (list_within_bound UINT_MOD l_up )) ,
  (UIntArray.full rp_pre n_pre l_rp )
|--
  (UIntArray.seg rp_pre 0 n_pre (sublist (0) (n_pre) (l_rp)) )
.

Definition mpn_submul_1_entail_wit_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l_up 0) * vl_pre ))) (PreH2 : (i < n_pre)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : ((Zlength (l_done)) = i)) (PreH10 : ((Zlength (l_rp)) = n_pre)) (PreH11 : ((Zlength (l_up)) = n_pre)) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (list_within_bound UINT_MOD l_rp )) (PreH14 : (list_within_bound UINT_MOD l_up )) (PreH15 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) ,
  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l_up )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l_up 0))
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
|--
  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ ((Znth i l_up 0) <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ ((Znth i l_up 0) >= 0) ” 
  &&  “ (cl >= 0) ” 
  &&  “ (vl_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l_up 0) * vl_pre )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ”
  &&  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l_up )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l_up 0))
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
.

Definition mpn_submul_1_entail_wit_3 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w0_value)) (PreH2 : (w0_value <= UINT_MAX)) (PreH3 : ((Znth i l_up 0) <= UINT_MAX)) (PreH4 : (w1_value <= UINT_MAX)) (PreH5 : ((Znth i l_up 0) >= 0)) (PreH6 : (cl >= 0)) (PreH7 : (vl_pre >= 0)) (PreH8 : (w1_value >= 0)) (PreH9 : (i <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (i >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l_up 0) * vl_pre ))) (PreH14 : (i < n_pre)) (PreH15 : (0 <= vl_pre)) (PreH16 : (vl_pre <= UINT_MAX)) (PreH17 : (0 <= i)) (PreH18 : (i <= n_pre)) (PreH19 : (0 <= cl)) (PreH20 : (cl <= UINT_MAX)) (PreH21 : ((Zlength (l_done)) = i)) (PreH22 : ((Zlength (l_rp)) = n_pre)) (PreH23 : ((Zlength (l_up)) = n_pre)) (PreH24 : (list_within_bound UINT_MOD l_done )) (PreH25 : (list_within_bound UINT_MOD l_rp )) (PreH26 : (list_within_bound UINT_MOD l_up )) (PreH27 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) ,
  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  (UIntArray.full up_pre n_pre l_up )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l_up 0))
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
|--
  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ (w0_value >= 0) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ ((Znth i l_up 0) <= UINT_MAX) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ ((Znth i l_up 0) >= 0) ” 
  &&  “ (cl >= 0) ” 
  &&  “ (vl_pre >= 0) ” 
  &&  “ (w1_value >= 0) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l_up 0) * vl_pre )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ”
  &&  ((( &( "hpl" ) )) # UInt  |-> w1_value)
  **  ((( &( "lpl" ) )) # UInt  |-> w0_value)
  **  (UIntArray.full up_pre n_pre l_up )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "vl" ) )) # UInt  |-> vl_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "cl" ) )) # UInt  |-> cl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l_up 0))
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
.

Definition mpn_submul_1_entail_wit_4 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done_2: (@list Z)) (cl: Z) (i: Z) (w0_value: Z) (w1_value: Z) (PreH1 : (0 <= w1_value)) (PreH2 : (w1_value <= UINT_MAX)) (PreH3 : (w0_value >= 0)) (PreH4 : (0 <= w0_value)) (PreH5 : (w0_value <= UINT_MAX)) (PreH6 : ((Znth i l_up 0) <= UINT_MAX)) (PreH7 : (w1_value <= UINT_MAX)) (PreH8 : ((Znth i l_up 0) >= 0)) (PreH9 : (cl >= 0)) (PreH10 : (vl_pre >= 0)) (PreH11 : (w1_value >= 0)) (PreH12 : (i <= INT_MAX)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (i >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (((w1_value * UINT_MOD ) + w0_value ) = ((Znth i l_up 0) * vl_pre ))) (PreH17 : (i < n_pre)) (PreH18 : (0 <= vl_pre)) (PreH19 : (vl_pre <= UINT_MAX)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= cl)) (PreH23 : (cl <= UINT_MAX)) (PreH24 : ((Zlength (l_done_2)) = i)) (PreH25 : ((Zlength (l_rp)) = n_pre)) (PreH26 : ((Zlength (l_up)) = n_pre)) (PreH27 : (list_within_bound UINT_MOD l_done_2 )) (PreH28 : (list_within_bound UINT_MOD l_rp )) (PreH29 : (list_within_bound UINT_MOD l_up )) (PreH30 : (((list_to_Z (UINT_MOD) (l_done_2)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) ,
  (UIntArray.full up_pre n_pre l_up )
  **  ((( &( "ul" ) )) # UInt  |-> (Znth i l_up 0))
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= w0_value) ” 
  &&  “ (w0_value <= UINT_MAX) ” 
  &&  “ (0 <= w1_value) ” 
  &&  “ (w1_value <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ” 
  &&  “ (((w1_value * UINT_MOD ) + w0_value ) = ((Znth (i) (l_up) (0)) * vl_pre )) ”
  &&  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
.

Definition mpn_submul_1_entail_wit_5_1 := 
(
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done_2)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done_2)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ((0 + hpl ) + 0 )) ” 
  &&  “ (((0 + hpl ) + 0 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (((0 + hpl ) + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up)))) * vl_pre ) )) ”
  &&  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
) \/
(
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done_2)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done_2)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ((0 + hpl ) + 0 )) ” 
  &&  “ (((0 + hpl ) + 0 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (((0 + hpl ) + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up)))) * vl_pre ) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_rp)) )
).

Definition mpn_submul_1_entail_wit_5_2 := 
(
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done_2)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done_2)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unsigned_last_nbits (((0 + hpl ) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((0 + hpl ) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - ((unsigned_last_nbits (((0 + hpl ) + 1 )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up)))) * vl_pre ) )) ”
  &&  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
) \/
(
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done_2)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done_2)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unsigned_last_nbits (((0 + hpl ) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((0 + hpl ) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - ((unsigned_last_nbits (((0 + hpl ) + 1 )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up)))) * vl_pre ) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_rp)) )
).

Definition mpn_submul_1_entail_wit_5_3 := 
(
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done_2)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done_2)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ((unsigned_last_nbits ((1 + hpl )) (32)) + 0 )) ” 
  &&  “ (((unsigned_last_nbits ((1 + hpl )) (32)) + 0 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (((unsigned_last_nbits ((1 + hpl )) (32)) + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up)))) * vl_pre ) )) ”
  &&  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
) \/
(
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done_2)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done_2)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= ((unsigned_last_nbits ((1 + hpl )) (32)) + 0 )) ” 
  &&  “ (((unsigned_last_nbits ((1 + hpl )) (32)) + 0 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (((unsigned_last_nbits ((1 + hpl )) (32)) + 0 ) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up)))) * vl_pre ) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_rp)) )
).

Definition mpn_submul_1_entail_wit_5_4 := 
(
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done_2)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done_2)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  ((( &( "lpl" ) )) # UInt  |-> (unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)))
  **  ((( &( "hpl" ) )) # UInt  |-> hpl)
  **  ((( &( "ul" ) )) # UInt  |-> (Znth (i) (l_up) (0)))
  **  ((( &( "rl" ) )) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((1 + hpl )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((1 + hpl )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - ((unsigned_last_nbits (((unsigned_last_nbits ((1 + hpl )) (32)) + 1 )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up)))) * vl_pre ) )) ”
  &&  ((( &( "ul" ) )) # UInt  |->_)
  **  ((( &( "lpl" ) )) # UInt  |->_)
  **  ((( &( "hpl" ) )) # UInt  |->_)
  **  ((( &( "rl" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 (i + 1 ) l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
) \/
(
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done_2: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done_2)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done_2)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (replace_Znth ((i - i )) ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32))) ((sublist (i) (n_pre) (l_rp)))) )
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unsigned_last_nbits (((unsigned_last_nbits ((1 + hpl )) (32)) + 1 )) (32))) ” 
  &&  “ ((unsigned_last_nbits (((unsigned_last_nbits ((1 + hpl )) (32)) + 1 )) (32)) <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = (i + 1 )) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - ((unsigned_last_nbits (((unsigned_last_nbits ((1 + hpl )) (32)) + 1 )) (32)) * (Z.pow (UINT_MOD) ((i + 1 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) ((i + 1 )) (l_up)))) * vl_pre ) )) ”
  &&  (UIntArray.seg rp_pre 0 (i + 1 ) l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_rp)) )
).

Definition mpn_submul_1_return_wit_1 := 
(
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= vl_pre)) (PreH3 : (vl_pre <= UINT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cl)) (PreH7 : (cl <= UINT_MAX)) (PreH8 : ((Zlength (l_done)) = i)) (PreH9 : ((Zlength (l_rp)) = n_pre)) (PreH10 : ((Zlength (l_up)) = n_pre)) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (list_within_bound UINT_MOD l_rp )) (PreH13 : (list_within_bound UINT_MOD l_up )) (PreH14 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) ,
  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  EX (val_out: Z)  (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_out)) = val_out) ” 
  &&  “ ((val_out - (cl * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_rp)) - ((list_to_Z (UINT_MOD) (l_up)) * vl_pre ) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
  **  (UIntArray.full up_pre n_pre l_up )
) \/
(
forall (vl_pre: Z) (n_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= vl_pre)) (PreH3 : (vl_pre <= UINT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cl)) (PreH7 : (cl <= UINT_MAX)) (PreH8 : ((Zlength (l_done)) = i)) (PreH9 : ((Zlength (l_rp)) = n_pre)) (PreH10 : ((Zlength (l_up)) = n_pre)) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (list_within_bound UINT_MOD l_rp )) (PreH13 : (list_within_bound UINT_MOD l_up )) (PreH14 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) ,
  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) - (cl * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_rp)) - ((list_to_Z (UINT_MOD) (l_up)) * vl_pre ) )) ”
  &&  (UIntArray.full rp_pre n_pre l_out )
).

Definition mpn_submul_1_partial_solve_wit_1 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= vl_pre)) (PreH3 : (vl_pre <= UINT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cl)) (PreH7 : (cl <= UINT_MAX)) (PreH8 : ((Zlength (l_done)) = i)) (PreH9 : ((Zlength (l_rp)) = n_pre)) (PreH10 : ((Zlength (l_up)) = n_pre)) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (list_within_bound UINT_MOD l_rp )) (PreH13 : (list_within_bound UINT_MOD l_up )) (PreH14 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) ,
  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ”
  &&  (((up_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth i l_up 0))
  **  (UIntArray.missing_i up_pre i 0 n_pre l_up )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
.

Definition mpn_submul_1_partial_solve_wit_2 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (cl: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= vl_pre)) (PreH3 : (vl_pre <= UINT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= cl)) (PreH7 : (cl <= UINT_MAX)) (PreH8 : ((Zlength (l_done)) = i)) (PreH9 : ((Zlength (l_rp)) = n_pre)) (PreH10 : ((Zlength (l_up)) = n_pre)) (PreH11 : (list_within_bound UINT_MOD l_done )) (PreH12 : (list_within_bound UINT_MOD l_rp )) (PreH13 : (list_within_bound UINT_MOD l_up )) (PreH14 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) ,
  (UIntArray.full up_pre n_pre l_up )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ”
  &&  (UIntArray.full up_pre n_pre l_up )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
.

Definition mpn_submul_1_partial_solve_wit_3 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH2 : (0 <= vl_pre)) (PreH3 : (vl_pre <= UINT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= cl)) (PreH7 : (cl <= UINT_MAX)) (PreH8 : (0 <= lpl)) (PreH9 : (lpl <= UINT_MAX)) (PreH10 : (0 <= hpl)) (PreH11 : (hpl <= UINT_MAX)) (PreH12 : ((Zlength (l_done)) = i)) (PreH13 : ((Zlength (l_rp)) = n_pre)) (PreH14 : ((Zlength (l_up)) = n_pre)) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (list_within_bound UINT_MOD l_rp )) (PreH17 : (list_within_bound UINT_MOD l_up )) (PreH18 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH19 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.missing_i rp_pre i i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
.

Definition mpn_submul_1_partial_solve_wit_4 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH2 : (0 <= vl_pre)) (PreH3 : (vl_pre <= UINT_MAX)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= cl)) (PreH7 : (cl <= UINT_MAX)) (PreH8 : (0 <= lpl)) (PreH9 : (lpl <= UINT_MAX)) (PreH10 : (0 <= hpl)) (PreH11 : (hpl <= UINT_MAX)) (PreH12 : ((Zlength (l_done)) = i)) (PreH13 : ((Zlength (l_rp)) = n_pre)) (PreH14 : ((Zlength (l_up)) = n_pre)) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (list_within_bound UINT_MOD l_rp )) (PreH17 : (list_within_bound UINT_MOD l_up )) (PreH18 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH19 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((unsigned_last_nbits ((lpl + cl )) (32)) < cl) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))
  **  (UIntArray.missing_i rp_pre i i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
.

Definition mpn_submul_1_partial_solve_wit_5 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0)) ” 
  &&  “ ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
.

Definition mpn_submul_1_partial_solve_wit_6 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0)) ” 
  &&  “ ((unsigned_last_nbits ((lpl + cl )) (32)) >= cl) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
.

Definition mpn_submul_1_partial_solve_wit_7 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) <= (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0)) ” 
  &&  “ ((unsigned_last_nbits ((lpl + cl )) (32)) < cl) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
.

Definition mpn_submul_1_partial_solve_wit_8 := 
forall (vl_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (l_up: (@list Z)) (l_rp: (@list Z)) (l_done: (@list Z)) (i: Z) (cl: Z) (lpl: Z) (hpl: Z) (PreH1 : ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0))) (PreH2 : ((unsigned_last_nbits ((lpl + cl )) (32)) < cl)) (PreH3 : (0 <= vl_pre)) (PreH4 : (vl_pre <= UINT_MAX)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= cl)) (PreH8 : (cl <= UINT_MAX)) (PreH9 : (0 <= lpl)) (PreH10 : (lpl <= UINT_MAX)) (PreH11 : (0 <= hpl)) (PreH12 : (hpl <= UINT_MAX)) (PreH13 : ((Zlength (l_done)) = i)) (PreH14 : ((Zlength (l_rp)) = n_pre)) (PreH15 : ((Zlength (l_up)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (list_within_bound UINT_MOD l_rp )) (PreH18 : (list_within_bound UINT_MOD l_up )) (PreH19 : (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) ))) (PreH20 : (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre ))) ,
  (UIntArray.seg rp_pre i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
|--
  “ ((unsigned_last_nbits (((Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0) - (unsigned_last_nbits ((lpl + cl )) (32)) )) (32)) > (Znth (i - i ) (sublist (i) (n_pre) (l_rp)) 0)) ” 
  &&  “ ((unsigned_last_nbits ((lpl + cl )) (32)) < cl) ” 
  &&  “ (0 <= vl_pre) ” 
  &&  “ (vl_pre <= UINT_MAX) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= cl) ” 
  &&  “ (cl <= UINT_MAX) ” 
  &&  “ (0 <= lpl) ” 
  &&  “ (lpl <= UINT_MAX) ” 
  &&  “ (0 <= hpl) ” 
  &&  “ (hpl <= UINT_MAX) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ ((Zlength (l_rp)) = n_pre) ” 
  &&  “ ((Zlength (l_up)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (list_within_bound UINT_MOD l_rp ) ” 
  &&  “ (list_within_bound UINT_MOD l_up ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_done)) - (cl * (Z.pow (UINT_MOD) (i)) ) ) = ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_rp)))) - ((list_to_Z (UINT_MOD) ((sublist (0) (i) (l_up)))) * vl_pre ) )) ” 
  &&  “ (((hpl * UINT_MOD ) + lpl ) = ((Znth (i) (l_up) (0)) * vl_pre )) ”
  &&  (((rp_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp_pre i i n_pre (sublist (i) (n_pre) (l_rp)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.full up_pre n_pre l_up )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_submul_1_safety_wit_1 : mpn_submul_1_safety_wit_1.
Axiom proof_of_mpn_submul_1_safety_wit_2 : mpn_submul_1_safety_wit_2.
Axiom proof_of_mpn_submul_1_safety_wit_3 : mpn_submul_1_safety_wit_3.
Axiom proof_of_mpn_submul_1_safety_wit_4 : mpn_submul_1_safety_wit_4.
Axiom proof_of_mpn_submul_1_safety_wit_5 : mpn_submul_1_safety_wit_5.
Axiom proof_of_mpn_submul_1_safety_wit_6 : mpn_submul_1_safety_wit_6.
Axiom proof_of_mpn_submul_1_safety_wit_7 : mpn_submul_1_safety_wit_7.
Axiom proof_of_mpn_submul_1_safety_wit_8 : mpn_submul_1_safety_wit_8.
Axiom proof_of_mpn_submul_1_safety_wit_9 : mpn_submul_1_safety_wit_9.
Axiom proof_of_mpn_submul_1_safety_wit_10 : mpn_submul_1_safety_wit_10.
Axiom proof_of_mpn_submul_1_entail_wit_1 : mpn_submul_1_entail_wit_1.
Axiom proof_of_mpn_submul_1_entail_wit_2 : mpn_submul_1_entail_wit_2.
Axiom proof_of_mpn_submul_1_entail_wit_3 : mpn_submul_1_entail_wit_3.
Axiom proof_of_mpn_submul_1_entail_wit_4 : mpn_submul_1_entail_wit_4.
Axiom proof_of_mpn_submul_1_entail_wit_5_1 : mpn_submul_1_entail_wit_5_1.
Axiom proof_of_mpn_submul_1_entail_wit_5_2 : mpn_submul_1_entail_wit_5_2.
Axiom proof_of_mpn_submul_1_entail_wit_5_3 : mpn_submul_1_entail_wit_5_3.
Axiom proof_of_mpn_submul_1_entail_wit_5_4 : mpn_submul_1_entail_wit_5_4.
Axiom proof_of_mpn_submul_1_return_wit_1 : mpn_submul_1_return_wit_1.
Axiom proof_of_mpn_submul_1_partial_solve_wit_1 : mpn_submul_1_partial_solve_wit_1.
Axiom proof_of_mpn_submul_1_partial_solve_wit_2 : mpn_submul_1_partial_solve_wit_2.
Axiom proof_of_mpn_submul_1_partial_solve_wit_3 : mpn_submul_1_partial_solve_wit_3.
Axiom proof_of_mpn_submul_1_partial_solve_wit_4 : mpn_submul_1_partial_solve_wit_4.
Axiom proof_of_mpn_submul_1_partial_solve_wit_5 : mpn_submul_1_partial_solve_wit_5.
Axiom proof_of_mpn_submul_1_partial_solve_wit_6 : mpn_submul_1_partial_solve_wit_6.
Axiom proof_of_mpn_submul_1_partial_solve_wit_7 : mpn_submul_1_partial_solve_wit_7.
Axiom proof_of_mpn_submul_1_partial_solve_wit_8 : mpn_submul_1_partial_solve_wit_8.

End VC_Correct.
