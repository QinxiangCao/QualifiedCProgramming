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

(*----- Function mpn_copyd -----*)

Definition mpn_copyd_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  “ ((False \/ (True /\ (off_shifted = 0))) \/ (True /\ (off_shifted > 0))) ”
.

Definition mpn_copyd_safety_wit_2_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_copyd_safety_wit_3_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_copyd_safety_wit_4_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (off_shifted = 0)) (PreH4 : ((-1) <= n_2)) (PreH5 : (n_2 < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = s_pre)) (PreH10 : (d_pre = s_pre)) (PreH11 : (off_shifted = 0)) (PreH12 : (n = (n_pre - 1 ))) (PreH13 : (n_pre >= 0)) (PreH14 : ((Zlength (l_shifted)) = n_pre)) (PreH15 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_2)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyd_safety_wit_5_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (k: Z) (n: Z) (k_2: Z) (n_2: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((-1) <= n_2)) (PreH4 : (n_2 < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (k_2 <= (n_2 + 1 ))) (PreH8 : ((n_2 + 1 ) <= k_2)) (PreH9 : (0 <= k_2)) (PreH10 : (k_2 <= n_pre)) (PreH11 : ((Zlength (l_shifted)) = n_pre)) (PreH12 : (list_within_bound UINT_MOD l_shifted )) (PreH13 : (off_shifted > 0)) (PreH14 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH15 : (n = (n_pre - 1 ))) (PreH16 : (n_pre >= 0)) (PreH17 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH18 : (k = n_pre)) (PreH19 : (k <= (n + 1 ))) (PreH20 : ((n + 1 ) <= k)) (PreH21 : ((Zlength (l_shifted)) = n_pre)) (PreH22 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_2)
  **  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyd_safety_wit_6_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n_2: Z) (n: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n)) (PreH7 : (n < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n_2 = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> s_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_copyd_safety_wit_7_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (off_shifted > 0)) (PreH11 : (0 <= n)) (PreH12 : (n < n_pre)) (PreH13 : (n_pre >= 0)) (PreH14 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (((d_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth (n - n ) (sublist (n) ((n + 1 )) (l_shifted)) 0))
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_copyd_entail_wit_1_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)) ,
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
|--
  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_entail_wit_2_off_pos := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)) ,
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
|--
  EX (k: Z) ,
  “ (off_shifted > 0) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (k = n_pre) ” 
  &&  “ (k <= ((n_pre - 1 ) + 1 )) ” 
  &&  “ (((n_pre - 1 ) + 1 ) <= k) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 k (sublist (0) (k) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k (off_shifted + k ) )
  **  (UIntArray.seg d_pre k n_pre (sublist (k) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)) ,
  TT && emp 
|--
  “ ((sublist (n_pre) (n_pre) (l_shifted)) = (@nil Z)) ”
  &&  emp
).

Definition mpn_copyd_entail_wit_2_off_pos_split_goal_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)) ,
  ((sublist (n_pre) (n_pre) (l_shifted)) = (@nil Z))
.

Definition mpn_copyd_entail_wit_3_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (off_shifted = 0)) (PreH4 : (n = (n_pre - 1 ))) (PreH5 : (n_pre >= 0)) (PreH6 : ((Zlength (l_shifted)) = n_pre)) (PreH7 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n = (n_pre - 1 )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_entail_wit_4_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (k: Z) (n: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH3 : (n = (n_pre - 1 ))) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (k = n_pre)) (PreH7 : (k <= (n + 1 ))) (PreH8 : ((n + 1 ) <= k)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 k (sublist (0) (k) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k (off_shifted + k ) )
  **  (UIntArray.seg d_pre k n_pre (sublist (k) (n_pre) (l_shifted)) )
|--
  EX (k_2: Z) ,
  “ (off_shifted > 0) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (k_2 <= (n + 1 )) ” 
  &&  “ ((n + 1 ) <= k_2) ” 
  &&  “ (0 <= k_2) ” 
  &&  “ (k_2 <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (n = (n_pre - 1 )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (k = n_pre) ” 
  &&  “ (k <= (n + 1 )) ” 
  &&  “ ((n + 1 ) <= k) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_entail_wit_5_off_pos := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (k: Z) (n_2: Z) (k_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n + 1 ))) (PreH9 : ((n + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n_2 = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n_2 + 1 ))) (PreH21 : ((n_2 + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (k: Z) (n_2: Z) (k_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n + 1 ))) (PreH9 : ((n + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n_2 = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n_2 + 1 ))) (PreH21 : ((n_2 + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_entail_wit_5_off_pos_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (k: Z) (n_2: Z) (k_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n + 1 ))) (PreH9 : ((n + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n_2 = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n_2 + 1 ))) (PreH21 : ((n_2 + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_entail_wit_6_off_zero := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n_2 >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n_2)) (PreH7 : (n_2 < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ ((-1) <= (n_2 - 1 )) ” 
  &&  “ ((n_2 - 1 ) < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n = (n_pre - 1 )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n_2 >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n_2)) (PreH7 : (n_2 < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_entail_wit_6_off_zero_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n_2 >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n_2)) (PreH7 : (n_2 < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_entail_wit_7_off_pos := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n_2: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n_2)) (PreH4 : (n_2 < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (off_shifted > 0)) (PreH11 : (0 <= n_2)) (PreH12 : (n_2 < n_pre)) (PreH13 : (n_pre >= 0)) (PreH14 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (((d_pre + (n_2 * sizeof(UINT)))) # UInt  |-> (Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0))
  **  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n_2 + 1 ) (off_shifted + n_2 ) )
  **  (UIntArray.seg d_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  EX (k_2: Z)  (k: Z)  (n: Z) ,
  “ (off_shifted > 0) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((-1) <= (n_2 - 1 )) ” 
  &&  “ ((n_2 - 1 ) < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (k_2 <= ((n_2 - 1 ) + 1 )) ” 
  &&  “ (((n_2 - 1 ) + 1 ) <= k_2) ” 
  &&  “ (0 <= k_2) ” 
  &&  “ (k_2 <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (n = (n_pre - 1 )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (k = n_pre) ” 
  &&  “ (k <= (n + 1 )) ” 
  &&  “ ((n + 1 ) <= k) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n_2: Z) (PreH1 : ((Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0) <= UINT_MAX)) (PreH2 : ((Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0) >= 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (off_shifted > 0)) (PreH5 : (0 <= n_2)) (PreH6 : (n_2 < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (off_shifted > 0)) (PreH13 : (0 <= n_2)) (PreH14 : (n_2 < n_pre)) (PreH15 : (n_pre >= 0)) (PreH16 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH17 : ((Zlength (l_shifted)) = n_pre)) (PreH18 : (list_within_bound UINT_MOD l_shifted )) ,
  (((d_pre + (n_2 * sizeof(UINT)))) # UInt  |-> (Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0))
  **  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n_2 + 1 ) (off_shifted + n_2 ) )
  **  (UIntArray.seg d_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  EX (k_2: Z) ,
  “ (off_shifted > 0) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((-1) <= (n_2 - 1 )) ” 
  &&  “ ((n_2 - 1 ) < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (k_2 <= ((n_2 - 1 ) + 1 )) ” 
  &&  “ (((n_2 - 1 ) + 1 ) <= k_2) ” 
  &&  “ (0 <= k_2) ” 
  &&  “ (k_2 <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (n_pre <= ((n_pre - 1 ) + 1 )) ” 
  &&  “ (((n_pre - 1 ) + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_return_wit_1_off_zero := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n_2)) (PreH6 : (n_2 < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.undef_seg s_pre 0 off_shifted )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n_2)) (PreH6 : (n_2 < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  TT && emp 
|--
  (UIntArray.undef_seg s_pre 0 off_shifted )
).

Definition mpn_copyd_return_wit_1_off_zero_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n_2)) (PreH6 : (n_2 < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  TT && emp 
|--
  (UIntArray.undef_seg s_pre 0 off_shifted )
.

Definition mpn_copyd_return_wit_2_off_pos := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (k: Z) (n: Z) (k_2: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n_2)) (PreH5 : (n_2 < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n_2 + 1 ))) (PreH9 : ((n_2 + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n + 1 ))) (PreH21 : ((n + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre k_2 (off_shifted + k_2 ) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.undef_seg s_pre 0 off_shifted )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (k: Z) (n: Z) (k_2: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n_2)) (PreH5 : (n_2 < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n_2 + 1 ))) (PreH9 : ((n_2 + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n + 1 ))) (PreH21 : ((n + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_return_wit_2_off_pos_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (k: Z) (n: Z) (k_2: Z) (n_2: Z) (PreH1 : (n_2 < 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((-1) <= n_2)) (PreH5 : (n_2 < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (k_2 <= (n_2 + 1 ))) (PreH9 : ((n_2 + 1 ) <= k_2)) (PreH10 : (0 <= k_2)) (PreH11 : (k_2 <= n_pre)) (PreH12 : ((Zlength (l_shifted)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_shifted )) (PreH14 : (off_shifted > 0)) (PreH15 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH16 : (n = (n_pre - 1 ))) (PreH17 : (n_pre >= 0)) (PreH18 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH19 : (k = n_pre)) (PreH20 : (k <= (n + 1 ))) (PreH21 : ((n + 1 ) <= k)) (PreH22 : ((Zlength (l_shifted)) = n_pre)) (PreH23 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 k_2 (sublist (0) (k_2) (l_shifted)) )
  **  (UIntArray.seg d_pre k_2 n_pre (sublist (k_2) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = n_pre)) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.full s_pre n_pre l_shifted )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
|--
  “ (n_pre >= 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.full s_pre n_pre l_shifted )
  **  (UIntArray.undef_seg s_pre n_pre (n_pre + off_shifted ) )
.

Definition mpn_copyd_partial_solve_wit_2_off_zero_pure := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n)) (PreH6 : (n < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n_2 = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (s_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ”
.

Definition mpn_copyd_partial_solve_wit_2_off_zero_aux := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n_2: Z) (n: Z) (PreH1 : (n >= 0)) (PreH2 : (d_pre = s_pre)) (PreH3 : (d_pre = s_pre)) (PreH4 : (off_shifted = 0)) (PreH5 : ((-1) <= n)) (PreH6 : (n < n_pre)) (PreH7 : (n_pre >= 0)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (d_pre = s_pre)) (PreH11 : (d_pre = s_pre)) (PreH12 : (off_shifted = 0)) (PreH13 : (n_2 = (n_pre - 1 ))) (PreH14 : (n_pre >= 0)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (s_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n >= 0) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n_2 = (n_pre - 1 )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  ((( &( "d" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_2_off_zero := mpn_copyd_partial_solve_wit_2_off_zero_pure -> mpn_copyd_partial_solve_wit_2_off_zero_aux.

Definition mpn_copyd_partial_solve_wit_3_off_pos_pure := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
.

Definition mpn_copyd_partial_solve_wit_3_off_pos_aux := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_3_off_pos := mpn_copyd_partial_solve_wit_3_off_pos_pure -> mpn_copyd_partial_solve_wit_3_off_pos_aux.

Definition mpn_copyd_partial_solve_wit_4_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (n_2: Z) (PreH1 : (s_pre = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (n_2 >= 0)) (PreH4 : (d_pre = s_pre)) (PreH5 : (d_pre = s_pre)) (PreH6 : (off_shifted = 0)) (PreH7 : ((-1) <= n_2)) (PreH8 : (n_2 < n_pre)) (PreH9 : (n_pre >= 0)) (PreH10 : ((Zlength (l_shifted)) = n_pre)) (PreH11 : (list_within_bound UINT_MOD l_shifted )) (PreH12 : (d_pre = s_pre)) (PreH13 : (d_pre = s_pre)) (PreH14 : (off_shifted = 0)) (PreH15 : (n = (n_pre - 1 ))) (PreH16 : (n_pre >= 0)) (PreH17 : ((Zlength (l_shifted)) = n_pre)) (PreH18 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = s_pre) ” 
  &&  “ (n_2 >= 0) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ ((-1) <= n_2) ” 
  &&  “ (n_2 < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n = (n_pre - 1 )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((s_pre + (n_2 * sizeof(UINT)))) # UInt  |-> (Znth (n_2 - n_2 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) 0))
  **  (UIntArray.missing_i s_pre n_2 n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_5_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (n_2: Z) (PreH1 : (d_pre = s_pre)) (PreH2 : (n_2 >= 0)) (PreH3 : (d_pre = s_pre)) (PreH4 : (d_pre = s_pre)) (PreH5 : (off_shifted = 0)) (PreH6 : ((-1) <= n_2)) (PreH7 : (n_2 < n_pre)) (PreH8 : (n_pre >= 0)) (PreH9 : ((Zlength (l_shifted)) = n_pre)) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (d_pre = s_pre)) (PreH12 : (d_pre = s_pre)) (PreH13 : (off_shifted = 0)) (PreH14 : (n = (n_pre - 1 ))) (PreH15 : (n_pre >= 0)) (PreH16 : ((Zlength (l_shifted)) = n_pre)) (PreH17 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = s_pre) ” 
  &&  “ (n_2 >= 0) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ ((-1) <= n_2) ” 
  &&  “ (n_2 < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (d_pre = s_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n = (n_pre - 1 )) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((s_pre + (n_2 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i s_pre n_2 n_2 (n_2 + 1 ) (sublist (n_2) ((n_2 + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n_2 (sublist (0) (n_2) (l_shifted)) )
  **  (UIntArray.seg s_pre (n_2 + 1 ) n_pre (sublist ((n_2 + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_6_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (off_shifted > 0)) (PreH11 : (0 <= n)) (PreH12 : (n < n_pre)) (PreH13 : (n_pre >= 0)) (PreH14 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((s_pre + (n * sizeof(UINT)))) # UInt  |-> (Znth (n - n ) (sublist (n) ((n + 1 )) (l_shifted)) 0))
  **  (UIntArray.missing_i s_pre n n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_partial_solve_wit_7_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (off_shifted > 0)) (PreH11 : (0 <= n)) (PreH12 : (n < n_pre)) (PreH13 : (n_pre >= 0)) (PreH14 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH15 : ((Zlength (l_shifted)) = n_pre)) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((d_pre + (n * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_which_implies_wit_1 := 
(
forall (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (s: Z) ,
  (UIntArray.full s n l_shifted )
  **  (UIntArray.undef_seg s n (n + off_shifted ) )
|--
  (UIntArray.seg s 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.undef_seg s n (n + off_shifted ) )
) \/
(
forall (l_shifted: (@list Z)) (n: Z) (s: Z) ,
  (UIntArray.full s n l_shifted )
|--
  (UIntArray.seg s 0 n (sublist (0) (n) (l_shifted)) )
).

Definition mpn_copyd_which_implies_wit_1_split_goal_spatial := 
forall (l_shifted: (@list Z)) (n: Z) (s: Z) ,
  (UIntArray.full s n l_shifted )
|--
  (UIntArray.seg s 0 n (sublist (0) (n) (l_shifted)) )
.

Definition mpn_copyd_which_implies_wit_2 := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (l_shifted: (@list Z)) (d: Z) (n: Z) (PreH1 : (d = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) ,
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (d = s_pre) ” 
  &&  “ (d_pre = s_pre) ”
  &&  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (l_shifted: (@list Z)) (d: Z) (n: Z) (PreH1 : (d = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) ,
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
).

Definition mpn_copyd_which_implies_wit_2_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (l_shifted: (@list Z)) (d: Z) (n: Z) (PreH1 : (d = s_pre)) (PreH2 : (d_pre = s_pre)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) ,
  (UIntArray.seg s_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
.

Definition mpn_copyd_which_implies_wit_3 := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre 0 (n + 1 ) (sublist (0) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
|--
  “ (d_pre = (s_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg s_pre 0 n (sublist (0) (n) (l_shifted)) )
  **  (UIntArray.seg s_pre n (n + 1 ) (sublist (n) ((n + 1 )) (l_shifted)) )
  **  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
  **  (UIntArray.seg d_pre (n + 1 ) n_pre (sublist ((n + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
|--
  “ ((sublist (0) ((n + 1 )) (l_shifted)) = (app ((sublist (0) (n) (l_shifted))) ((sublist (n) ((n + 1 )) (l_shifted))))) ” 
  &&  “ ((Zlength ((sublist (0) (n) (l_shifted)))) = (n - 0 )) ”
  &&  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
).

Definition mpn_copyd_which_implies_wit_3_split_goal_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
|--
  “ ((sublist (0) ((n + 1 )) (l_shifted)) = (app ((sublist (0) (n) (l_shifted))) ((sublist (n) ((n + 1 )) (l_shifted))))) ”
.

Definition mpn_copyd_which_implies_wit_3_split_goal_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
|--
  “ ((Zlength ((sublist (0) (n) (l_shifted)))) = (n - 0 )) ”
.

Definition mpn_copyd_which_implies_wit_3_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (n: Z) (PreH1 : (d_pre = (s_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= n)) (PreH4 : (n < n_pre)) (PreH5 : (n_pre >= 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.undef_seg s_pre (n + 1 ) ((off_shifted + n ) + 1 ) )
|--
  (UIntArray.undef_seg s_pre (n + 1 ) (off_shifted + n ) )
  **  (UIntArray.undef_seg d_pre n (n + 1 ) )
.

(*----- Function mpn_zero -----*)

Definition mpn_zero_safety_wit_1 := 
forall (n_pre: Z) (rp_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= INT_MAX)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.undef_seg rp_pre 0 n_pre )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_zero_safety_wit_2 := 
forall (n_pre: Z) (rp_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : ((-1) <= n)) (PreH2 : (n < n_pre)) (PreH3 : (n_pre >= 0)) (PreH4 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH5 : (list_within_bound UINT_MOD l_done )) (PreH6 : ((list_to_Z (UINT_MOD) (l_done)) = 0)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_zero_safety_wit_3 := 
forall (n_pre: Z) (rp_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.undef_seg rp_pre n (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_zero_safety_wit_4 := 
forall (n_pre: Z) (rp_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)) ,
  (((rp_pre + (n * sizeof(UINT)))) # UInt  |-> 0)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_zero_entail_wit_1 := 
(
forall (n_pre: Z) (rp_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= INT_MAX)) ,
  (UIntArray.undef_seg rp_pre 0 n_pre )
|--
  EX (l_done: (@list Z)) ,
  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.undef_seg rp_pre 0 ((n_pre - 1 ) + 1 ) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (n_pre: Z) (rp_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= INT_MAX)) ,
  TT && emp 
|--
  EX (l_done: (@list Z)) ,
  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
).

Definition mpn_zero_entail_wit_2 := 
(
forall (n_pre: Z) (rp_pre: Z) (l_done_2: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done_2)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done_2 )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done_2)) = 0)) ,
  (((rp_pre + (n * sizeof(UINT)))) # UInt  |-> 0)
  **  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ ((-1) <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((n - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.undef_seg rp_pre 0 ((n - 1 ) + 1 ) )
  **  (UIntArray.seg rp_pre ((n - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (n_pre: Z) (rp_pre: Z) (l_done_2: (@list Z)) (n: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (n >= 0)) (PreH4 : ((-1) <= n)) (PreH5 : (n < n_pre)) (PreH6 : (n_pre >= 0)) (PreH7 : ((Zlength (l_done_2)) = (n_pre - (n + 1 ) ))) (PreH8 : (list_within_bound UINT_MOD l_done_2 )) (PreH9 : ((list_to_Z (UINT_MOD) (l_done_2)) = 0)) ,
  (((rp_pre + (n * sizeof(UINT)))) # UInt  |-> 0)
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done_2 )
|--
  EX (l_done: (@list Z)) ,
  “ ((-1) <= (n - 1 )) ” 
  &&  “ ((n - 1 ) < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((n - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.seg rp_pre ((n - 1 ) + 1 ) n_pre l_done )
).

Definition mpn_zero_return_wit_1 := 
(
forall (n_pre: Z) (rp_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)) ,
  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ”
  &&  (UIntArray.full rp_pre n_pre l )
) \/
(
forall (n_pre: Z) (rp_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n < 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)) ,
  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  EX (l: (@list Z)) ,
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ”
  &&  (UIntArray.full rp_pre n_pre l )
).

Definition mpn_zero_partial_solve_wit_1 := 
forall (n_pre: Z) (rp_pre: Z) (PreH1 : (n_pre >= 0)) (PreH2 : (n_pre <= INT_MAX)) ,
  (UIntArray.undef_seg rp_pre 0 n_pre )
|--
  “ (n_pre >= 0) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  (UIntArray.undef_seg rp_pre 0 n_pre )
.

Definition mpn_zero_partial_solve_wit_2_pure := 
forall (n_pre: Z) (rp_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (0 <= n) ” 
  &&  “ (n < n_pre) ”
.

Definition mpn_zero_partial_solve_wit_2_aux := 
forall (n_pre: Z) (rp_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)) ,
  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (0 <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (n + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
.

Definition mpn_zero_partial_solve_wit_2 := mpn_zero_partial_solve_wit_2_pure -> mpn_zero_partial_solve_wit_2_aux.

Definition mpn_zero_partial_solve_wit_3 := 
forall (n_pre: Z) (rp_pre: Z) (l_done: (@list Z)) (n: Z) (PreH1 : (n >= 0)) (PreH2 : ((-1) <= n)) (PreH3 : (n < n_pre)) (PreH4 : (n_pre >= 0)) (PreH5 : ((Zlength (l_done)) = (n_pre - (n + 1 ) ))) (PreH6 : (list_within_bound UINT_MOD l_done )) (PreH7 : ((list_to_Z (UINT_MOD) (l_done)) = 0)) ,
  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.undef_seg rp_pre n (n + 1 ) )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
|--
  “ (n >= 0) ” 
  &&  “ ((-1) <= n) ” 
  &&  “ (n < n_pre) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (n + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_done)) = 0) ”
  &&  (((rp_pre + (n * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.seg rp_pre (n + 1 ) n_pre l_done )
.

Definition mpn_zero_which_implies_wit_1 := 
forall (n: Z) (rp: Z) ,
  (UIntArray.undef_seg rp 0 n )
|--
  (UIntArray.undef_seg rp 0 n )
.

Definition mpn_zero_which_implies_wit_2 := 
forall (n_pre: Z) (rp_pre: Z) (n: Z) (PreH1 : (0 <= n)) (PreH2 : (n < n_pre)) ,
  (UIntArray.undef_seg rp_pre 0 (n + 1 ) )
|--
  (UIntArray.undef_seg rp_pre 0 n )
  **  (UIntArray.undef_seg rp_pre n (n + 1 ) )
.

(*----- Function mpn_lshift -----*)

Definition mpn_lshift_safety_wit_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((False \/ (True /\ (off_shifted = 0))) \/ (True /\ (off_shifted > 0))) ”
.

Definition mpn_lshift_safety_wit_2_off_zero := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_lshift_safety_wit_3_off_pos := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_lshift_safety_wit_4_off_zero := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_lshift_safety_wit_5_off_zero := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_6_off_pos := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_lshift_safety_wit_7_off_pos := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_8_off_zero := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((32 - cnt_pre ) <= 31) ” 
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_lshift_safety_wit_9_off_pos := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ ((32 - cnt_pre ) <= 31) ” 
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_lshift_safety_wit_10_off_zero := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_11_off_pos := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  ((( &( "i" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "retval" ) )) # UInt  |-> (Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_12_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc_2 = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= i_2)) (PreH7 : (i_2 < n_pre)) (PreH8 : ((Zlength (l_up_shifted)) = n_pre)) (PreH9 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH10 : (list_within_bound UINT_MOD l_up_shifted )) (PreH11 : (list_within_bound UINT_MOD l_done_2 )) (PreH12 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH13 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH14 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH15 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH16 : (off_shifted = 0)) (PreH17 : (rp_pre = up_pre)) (PreH18 : (tnc = (32 - cnt_pre ))) (PreH19 : (1 <= cnt_pre)) (PreH20 : (cnt_pre < 32)) (PreH21 : (i = (n_pre - 1 ))) (PreH22 : (0 <= i)) (PreH23 : (i < n_pre)) (PreH24 : ((Zlength (l_up_shifted)) = n_pre)) (PreH25 : (l_done = (@nil Z))) (PreH26 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH27 : (list_within_bound UINT_MOD l_up_shifted )) (PreH28 : (list_within_bound UINT_MOD l_done )) (PreH29 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH30 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH31 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH32 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_13_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc_2 = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted > 0)) (PreH18 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH19 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH20 : (tnc = (32 - cnt_pre ))) (PreH21 : (1 <= cnt_pre)) (PreH22 : (cnt_pre < 32)) (PreH23 : (i = (n_pre - 1 ))) (PreH24 : (0 <= i)) (PreH25 : (i < n_pre)) (PreH26 : ((Zlength (l_up_shifted)) = n_pre)) (PreH27 : (l_done = (@nil Z))) (PreH28 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH29 : (list_within_bound UINT_MOD l_up_shifted )) (PreH30 : (list_within_bound UINT_MOD l_done )) (PreH31 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH32 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH33 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH34 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_14_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i_2: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i: Z) (tnc_2: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc_2 = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done = (@nil Z))) (PreH27 : ((Zlength (l_done)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_lshift_safety_wit_15_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc_2 = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i = (n_pre - 1 ))) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done = (@nil Z))) (PreH27 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_16_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i_2: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i: Z) (tnc_2: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc_2 = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH34 : (high_limb = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition mpn_lshift_safety_wit_17_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc_2 = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i = (n_pre - 1 ))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH33 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH34 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb_2)
  **  ((( &( "retval" ) )) # UInt  |-> retval_2)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb_2)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_18_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_lshift_safety_wit_19_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_lshift_safety_wit_20_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_21_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpn_lshift_safety_wit_22_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (tnc <= 31) ” 
  &&  “ (0 <= tnc) ”
.

Definition mpn_lshift_safety_wit_23_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (tnc <= 31) ” 
  &&  “ (0 <= tnc) ”
.

Definition mpn_lshift_safety_wit_24_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH9 : (0 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (replace_Znth (((i + 1 ) - (i + 1 ) )) ((Z.lor high_limb (Z.shiftr low_limb tnc))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_25_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (((rp_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb (Z.shiftr low_limb tnc)))
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_lshift_safety_wit_26_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (0 = 0)) (PreH3 : (off_shifted = 0)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (i = 0)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_safety_wit_27_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (0 = 0)) (PreH3 : (off_shifted > 0)) (PreH4 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (tnc = (32 - cnt_pre ))) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (0 <= low_limb)) (PreH10 : (low_limb <= UINT_MAX)) (PreH11 : (i = 0)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_lshift_entail_wit_1_off_zero := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ” 
  &&  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ” 
  &&  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
).

Definition mpn_lshift_entail_wit_1_off_zero_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_lshift_entail_wit_1_off_zero_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
.

Definition mpn_lshift_entail_wit_1_off_zero_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
.

Definition mpn_lshift_entail_wit_1_off_zero_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ”
.

Definition mpn_lshift_entail_wit_1_off_zero_split_goal_5 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_lshift_entail_wit_1_off_zero_split_goal_6 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
.

Definition mpn_lshift_entail_wit_1_off_zero_split_goal_spatial := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
.

Definition mpn_lshift_entail_wit_2_off_pos := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((n_pre - 1 ) = (n_pre - 1 )) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ” 
  &&  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre ((n_pre - 1 ) + 1 ) ((off_shifted + (n_pre - 1 ) ) + 1 ) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre l_done )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ” 
  &&  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
  &&  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
).

Definition mpn_lshift_entail_wit_2_off_pos_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_lshift_entail_wit_2_off_pos_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) cnt_pre)) (32)) = (unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ”
.

Definition mpn_lshift_entail_wit_2_off_pos_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Z.shiftr (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) (32 - cnt_pre )) = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) )) ”
.

Definition mpn_lshift_entail_wit_2_off_pos_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0) = (Znth ((n_pre - 1 )) (l_up_shifted) (0))) ”
.

Definition mpn_lshift_entail_wit_2_off_pos_split_goal_5 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_lshift_entail_wit_2_off_pos_split_goal_6 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ”
.

Definition mpn_lshift_entail_wit_2_off_pos_split_goal_spatial := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
|--
  (UIntArray.seg up_pre 0 ((n_pre - 1 ) + 1 ) (sublist (0) (((n_pre - 1 ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((n_pre - 1 ) + 1 ) n_pre (@nil Z) )
.

Definition mpn_lshift_entail_wit_3_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (i = (n_pre - 1 ))) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : (l_done = (@nil Z))) (PreH11 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done )
|--
  EX (l_done_2: (@list Z)) ,
  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_entail_wit_4_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (i = (n_pre - 1 ))) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : (l_done = (@nil Z))) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done )
|--
  EX (l_done_2: (@list Z)) ,
  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_entail_wit_5_off_zero_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb_2: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc_2 = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done_2 = (@nil Z))) (PreH27 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH32 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0)) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) <= UINT_MAX) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) = (Znth ((i - 1 )) (l_up_shifted) (0))) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb_2: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc_2 = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done_2 = (@nil Z))) (PreH27 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH32 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0)) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) <= UINT_MAX) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) = (Znth ((i - 1 )) (l_up_shifted) (0))) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
).

Definition mpn_lshift_entail_wit_6_off_pos_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb_2: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc_2 = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH34 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0)) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) <= UINT_MAX) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) = (Znth ((i - 1 )) (l_up_shifted) (0))) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre ((i - 1 ) + 2 ) ((off_shifted + (i - 1 ) ) + 2 ) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb_2: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (low_limb_2 = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc_2 = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (low_limb = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH34 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0)) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) <= UINT_MAX) ” 
  &&  “ ((Znth ((i - 1 ) - 0 ) (sublist (0) ((i + 1 )) (l_up_shifted)) 0) = (Znth ((i - 1 )) (l_up_shifted) (0))) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - ((i - 1 ) + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (((i - 1 ) + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - ((i - 1 ) + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (((i - 1 ) + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 ((i - 1 ) + 2 ) (sublist (0) (((i - 1 ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((i - 1 ) + 2 ) n_pre l_done )
).

Definition mpn_lshift_entail_wit_7_off_zero_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc_2 = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb_2)) (PreH7 : (low_limb_2 <= UINT_MAX)) (PreH8 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH9 : (0 <= i_2)) (PreH10 : ((i_2 + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done_3 )) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre (i_2 + 1 ) (i_2 + 2 ) (replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_shifted)))) )
  **  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z))  (high_limb: Z)  (retval: Z)  (low_limb: Z)  (l_done: (@list Z))  (i: Z)  (tnc: Z) ,
  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc_2 = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb_2)) (PreH7 : (low_limb_2 <= UINT_MAX)) (PreH8 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH9 : (0 <= i_2)) (PreH10 : ((i_2 + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done_3 )) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre (i_2 + 1 ) (i_2 + 2 ) (replace_Znth (((i_2 + 1 ) - (i_2 + 1 ) )) ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2))) ((sublist ((i_2 + 1 )) ((i_2 + 2 )) (l_up_shifted)))) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z)) ,
  “ (up_pre = rp_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
).

Definition mpn_lshift_entail_wit_8_off_pos_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc_2 = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb_2)) (PreH9 : (low_limb_2 <= UINT_MAX)) (PreH10 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH11 : (0 <= i_2)) (PreH12 : ((i_2 + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done_3 )) (PreH17 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH18 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (((rp_pre + ((i_2 + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)))
  **  (UIntArray.undef_seg up_pre (i_2 + 2 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg up_pre 0 (i_2 + 2 ) (sublist (0) ((i_2 + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z))  (high_limb: Z)  (retval: Z)  (low_limb: Z)  (l_done: (@list Z))  (i: Z)  (tnc: Z) ,
  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_3: (@list Z)) (tnc_2: Z) (low_limb_2: Z) (i_2: Z) (retval_2: Z) (high_limb_2: Z) (PreH1 : ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) <= UINT_MAX)) (PreH2 : ((Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)) >= 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (off_shifted > 0)) (PreH5 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (tnc_2 = (32 - cnt_pre ))) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (0 <= low_limb_2)) (PreH11 : (low_limb_2 <= UINT_MAX)) (PreH12 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH13 : (0 <= i_2)) (PreH14 : ((i_2 + 1 ) < n_pre)) (PreH15 : ((Zlength (l_up_shifted)) = n_pre)) (PreH16 : ((Zlength (l_done_3)) = (n_pre - (i_2 + 2 ) ))) (PreH17 : (list_within_bound UINT_MOD l_up_shifted )) (PreH18 : (list_within_bound UINT_MOD l_done_3 )) (PreH19 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH20 : (high_limb_2 = (unsigned_last_nbits (((Znth ((i_2 + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH21 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - (i_2 + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i_2 + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (((rp_pre + ((i_2 + 1 ) * sizeof(UINT)))) # UInt  |-> (Z.lor high_limb_2 (Z.shiftr low_limb_2 tnc_2)))
  **  (UIntArray.undef_seg up_pre (i_2 + 2 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg up_pre 0 (i_2 + 2 ) (sublist (0) ((i_2 + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 2 ) n_pre l_done_3 )
|--
  EX (l_done_2: (@list Z)) ,
  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ ((((unsigned_last_nbits ((Z.shiftl low_limb_2 cnt_pre)) (32)) + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength ((@nil Z))) = (n_pre - ((n_pre - 1 ) + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((((unsigned_last_nbits (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)) + ((list_to_Z (UINT_MOD) ((@nil Z))) * UINT_MOD ) ) + (((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) * (Z.pow (UINT_MOD) ((n_pre - (n_pre - 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((n_pre - 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
).

Definition mpn_lshift_entail_wit_9_off_zero_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc_2 = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done_2 = (@nil Z))) (PreH27 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH32 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_3 )) (PreH13 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc_2 = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i_2 = (n_pre - 1 ))) (PreH23 : (0 <= i_2)) (PreH24 : (i_2 < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done_2 = (@nil Z))) (PreH27 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done_2 )) (PreH30 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH31 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH32 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
).

Definition mpn_lshift_entail_wit_10_off_pos_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc_2 = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH34 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 1 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done_2: (@list Z)) (tnc_2: Z) (i_2: Z) (low_limb_2: Z) (retval_2: Z) (high_limb_2: Z) (high_limb: Z) (retval: Z) (low_limb: Z) (l_done_3: (@list Z)) (i: Z) (tnc: Z) (PreH1 : (i <= 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_3)) = (n_pre - (i + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_3 )) (PreH14 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done_3)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc_2 = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i_2 = (n_pre - 1 ))) (PreH25 : (0 <= i_2)) (PreH26 : (i_2 < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done_2 = (@nil Z))) (PreH29 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done_2 )) (PreH32 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH33 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH34 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) n_pre l_done_3 )
|--
  EX (l_done: (@list Z)) ,
  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
).

Definition mpn_lshift_return_wit_1_off_zero_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.full up_pre 1 (replace_Znth (0) (high_limb) ((sublist (0) (1) (l_up_shifted)))) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre 0 off_shifted )
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.full up_pre 1 (replace_Znth (0) (high_limb) ((sublist (0) (1) (l_up_shifted)))) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre 0 off_shifted )
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
).

Definition mpn_lshift_return_wit_2_off_pos_inv := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (i = 0)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> high_limb)
  **  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre 0 off_shifted )
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (high_limb <= UINT_MAX)) (PreH2 : (high_limb >= 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (off_shifted > 0)) (PreH5 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (tnc = (32 - cnt_pre ))) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (0 <= low_limb)) (PreH11 : (low_limb <= UINT_MAX)) (PreH12 : (i = 0)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |-> high_limb)
  **  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre 0 off_shifted )
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
).

Definition mpn_lshift_partial_solve_wit_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.full up_pre n_pre l_up_shifted )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
|--
  “ (n_pre > 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  (UIntArray.full up_pre n_pre l_up_shifted )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
.

Definition mpn_lshift_partial_solve_wit_2_off_zero := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted = 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
|--
  “ (n_pre > 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (off_shifted = 0) ”
  &&  (((up_pre + ((n_pre - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre (n_pre - 1 ) 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
.

Definition mpn_lshift_partial_solve_wit_3_off_pos := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (off_shifted >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) (PreH9 : (off_shifted > 0)) ,
  (UIntArray.seg up_pre 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
|--
  “ (n_pre > 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (off_shifted > 0) ”
  &&  (((up_pre + ((n_pre - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((n_pre - 1 ) - 0 ) (sublist (0) (n_pre) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre (n_pre - 1 ) 0 n_pre (sublist (0) (n_pre) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre n_pre (n_pre + off_shifted ) )
.

Definition mpn_lshift_partial_solve_wit_4_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc_2 = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= i_2)) (PreH8 : (i_2 < n_pre)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done_2 )) (PreH13 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH14 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH15 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH16 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH17 : (off_shifted = 0)) (PreH18 : (rp_pre = up_pre)) (PreH19 : (tnc = (32 - cnt_pre ))) (PreH20 : (1 <= cnt_pre)) (PreH21 : (cnt_pre < 32)) (PreH22 : (i = (n_pre - 1 ))) (PreH23 : (0 <= i)) (PreH24 : (i < n_pre)) (PreH25 : ((Zlength (l_up_shifted)) = n_pre)) (PreH26 : (l_done = (@nil Z))) (PreH27 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH28 : (list_within_bound UINT_MOD l_up_shifted )) (PreH29 : (list_within_bound UINT_MOD l_done )) (PreH30 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH31 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH32 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH33 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (i_2 > 0) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((up_pre + ((i_2 - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((i_2 - 1 ) - 0 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre (i_2 - 1 ) 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_partial_solve_wit_5_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (i: Z) (low_limb: Z) (retval: Z) (high_limb: Z) (high_limb_2: Z) (retval_2: Z) (low_limb_2: Z) (l_done_2: (@list Z)) (i_2: Z) (tnc_2: Z) (PreH1 : (i_2 > 0)) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc_2 = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < n_pre)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done_2 )) (PreH14 : (low_limb_2 = (Znth (i_2) (l_up_shifted) (0)))) (PreH15 : (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) ))) (PreH16 : (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) (PreH18 : (off_shifted > 0)) (PreH19 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH20 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH21 : (tnc = (32 - cnt_pre ))) (PreH22 : (1 <= cnt_pre)) (PreH23 : (cnt_pre < 32)) (PreH24 : (i = (n_pre - 1 ))) (PreH25 : (0 <= i)) (PreH26 : (i < n_pre)) (PreH27 : ((Zlength (l_up_shifted)) = n_pre)) (PreH28 : (l_done = (@nil Z))) (PreH29 : ((Zlength (l_done)) = (n_pre - (i + 1 ) ))) (PreH30 : (list_within_bound UINT_MOD l_up_shifted )) (PreH31 : (list_within_bound UINT_MOD l_done )) (PreH32 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH33 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH34 : (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH35 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
|--
  “ (i_2 > 0) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc_2 = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done_2)) = (n_pre - (i_2 + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done_2 ) ” 
  &&  “ (low_limb_2 = (Znth (i_2) (l_up_shifted) (0))) ” 
  &&  “ (retval_2 = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc_2)) )) ” 
  &&  “ (high_limb_2 = (unsigned_last_nbits (((Znth (i_2) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb_2 + ((list_to_Z (UINT_MOD) (l_done_2)) * UINT_MOD ) ) + (retval_2 * (Z.pow (UINT_MOD) ((n_pre - i_2 ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i_2) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (i = (n_pre - 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 1 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth (i) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - i ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist (i) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((up_pre + ((i_2 - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((i_2 - 1 ) - 0 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre (i_2 - 1 ) 0 (i_2 + 1 ) (sublist (0) ((i_2 + 1 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i_2 + 1 ) ((off_shifted + i_2 ) + 1 ) )
  **  (UIntArray.seg rp_pre (i_2 + 1 ) n_pre l_done_2 )
.

Definition mpn_lshift_partial_solve_wit_6_off_zero_inv_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH9 : (0 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_6_off_zero_inv_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH9 : (0 <= i)) (PreH10 : ((i + 1 ) < n_pre)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_6_off_zero_inv := mpn_lshift_partial_solve_wit_6_off_zero_inv_pure -> mpn_lshift_partial_solve_wit_6_off_zero_inv_aux.

Definition mpn_lshift_partial_solve_wit_7_off_pos_inv_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ”
.

Definition mpn_lshift_partial_solve_wit_7_off_pos_inv_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_7_off_pos_inv := mpn_lshift_partial_solve_wit_7_off_pos_inv_pure -> mpn_lshift_partial_solve_wit_7_off_pos_inv_aux.

Definition mpn_lshift_partial_solve_wit_8_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (rp_pre = up_pre)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH10 : (0 <= i)) (PreH11 : ((i + 1 ) < n_pre)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH18 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((up_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre (i + 1 ) (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_9_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (low_limb = (Znth (i) (l_up_shifted) (0)))) (PreH11 : (0 <= i)) (PreH12 : ((i + 1 ) < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = n_pre)) (PreH14 : ((Zlength (l_done)) = (n_pre - (i + 2 ) ))) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH18 : (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32)))) (PreH19 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (low_limb = (Znth (i) (l_up_shifted) (0))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - (i + 2 ) )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (high_limb = (unsigned_last_nbits (((Znth ((i + 1 )) (l_up_shifted) (0)) * (Z.pow (2) (cnt_pre)) )) (32))) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) ((n_pre - (i + 1 ) ))) ) ) = ((list_to_Z (UINT_MOD) ((sublist ((i + 1 )) (n_pre) (l_up_shifted)))) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((rp_pre + ((i + 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 2 ) n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_10_off_zero_inv_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 = 0) ”
.

Definition mpn_lshift_partial_solve_wit_10_off_zero_inv_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted = 0)) (PreH2 : (rp_pre = up_pre)) (PreH3 : (tnc = (32 - cnt_pre ))) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (0 <= low_limb)) (PreH7 : (low_limb <= UINT_MAX)) (PreH8 : (i = 0)) (PreH9 : ((Zlength (l_up_shifted)) = n_pre)) (PreH10 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH11 : (list_within_bound UINT_MOD l_up_shifted )) (PreH12 : (list_within_bound UINT_MOD l_done )) (PreH13 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH14 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (up_pre = up_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  ((( &( "rp" ) )) # Ptr  |-> up_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_10_off_zero_inv := mpn_lshift_partial_solve_wit_10_off_zero_inv_pure -> mpn_lshift_partial_solve_wit_10_off_zero_inv_aux.

Definition mpn_lshift_partial_solve_wit_11_off_pos_inv_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (i = 0)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 = 0) ”
.

Definition mpn_lshift_partial_solve_wit_11_off_pos_inv_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (off_shifted > 0)) (PreH2 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (tnc = (32 - cnt_pre ))) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (0 <= low_limb)) (PreH8 : (low_limb <= UINT_MAX)) (PreH9 : (i = 0)) (PreH10 : ((Zlength (l_up_shifted)) = n_pre)) (PreH11 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH12 : (list_within_bound UINT_MOD l_up_shifted )) (PreH13 : (list_within_bound UINT_MOD l_done )) (PreH14 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH15 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  ((( &( "i" ) )) # Int  |-> 0)
  **  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_11_off_pos_inv := mpn_lshift_partial_solve_wit_11_off_pos_inv_pure -> mpn_lshift_partial_solve_wit_11_off_pos_inv_aux.

Definition mpn_lshift_partial_solve_wit_12_off_zero_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (up_pre = up_pre)) (PreH2 : (0 = 0)) (PreH3 : (off_shifted = 0)) (PreH4 : (rp_pre = up_pre)) (PreH5 : (tnc = (32 - cnt_pre ))) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (0 <= low_limb)) (PreH9 : (low_limb <= UINT_MAX)) (PreH10 : (i = 0)) (PreH11 : ((Zlength (l_up_shifted)) = n_pre)) (PreH12 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_done )) (PreH15 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH16 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (off_shifted = 0) ” 
  &&  “ (rp_pre = up_pre) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((up_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i up_pre 0 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
.

Definition mpn_lshift_partial_solve_wit_13_off_pos_inv := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_done: (@list Z)) (tnc: Z) (low_limb: Z) (i: Z) (retval: Z) (high_limb: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (0 = 0)) (PreH3 : (off_shifted > 0)) (PreH4 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (tnc = (32 - cnt_pre ))) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (0 <= low_limb)) (PreH10 : (low_limb <= UINT_MAX)) (PreH11 : (i = 0)) (PreH12 : ((Zlength (l_up_shifted)) = n_pre)) (PreH13 : ((Zlength (l_done)) = (n_pre - 1 ))) (PreH14 : (list_within_bound UINT_MOD l_up_shifted )) (PreH15 : (list_within_bound UINT_MOD l_done )) (PreH16 : (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) ))) (PreH17 : (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) ))) ,
  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (0 <= low_limb) ” 
  &&  “ (low_limb <= UINT_MAX) ” 
  &&  “ (i = 0) ” 
  &&  “ ((Zlength (l_up_shifted)) = n_pre) ” 
  &&  “ ((Zlength (l_done)) = (n_pre - 1 )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (retval = ((Znth ((n_pre - 1 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (tnc)) )) ” 
  &&  “ (((high_limb + ((list_to_Z (UINT_MOD) (l_done)) * UINT_MOD ) ) + (retval * (Z.pow (UINT_MOD) (n_pre)) ) ) = ((list_to_Z (UINT_MOD) (l_up_shifted)) * (Z.pow (2) (cnt_pre)) )) ”
  &&  (((rp_pre + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 1 n_pre l_done )
.

Definition mpn_lshift_which_implies_wit_1 := 
(
forall (off_shifted: Z) (l_up_shifted: (@list Z)) (n: Z) (up: Z) ,
  (UIntArray.full up n l_up_shifted )
  **  (UIntArray.undef_seg up n (n + off_shifted ) )
|--
  (UIntArray.seg up 0 n (sublist (0) (n) (l_up_shifted)) )
  **  (UIntArray.undef_seg up n (n + off_shifted ) )
) \/
(
forall (l_up_shifted: (@list Z)) (n: Z) (up: Z) ,
  (UIntArray.full up n l_up_shifted )
|--
  (UIntArray.seg up 0 n (sublist (0) (n) (l_up_shifted)) )
).

Definition mpn_lshift_which_implies_wit_1_split_goal_spatial := 
forall (l_up_shifted: (@list Z)) (n: Z) (up: Z) ,
  (UIntArray.full up n l_up_shifted )
|--
  (UIntArray.seg up 0 n (sublist (0) (n) (l_up_shifted)) )
.

Definition mpn_lshift_which_implies_wit_2 := 
(
forall (n_pre: Z) (up_pre: Z) (l_up_shifted: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : ((i + 1 ) < n_pre)) ,
  (UIntArray.seg up_pre 0 (i + 2 ) (sublist (0) ((i + 2 )) (l_up_shifted)) )
|--
  “ (rp = up_pre) ”
  &&  (UIntArray.seg up_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up_pre (i + 1 ) (i + 2 ) (sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)) )
) \/
(
forall (n_pre: Z) (up_pre: Z) (l_up_shifted: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : ((i + 1 ) < n_pre)) ,
  TT && emp 
|--
  “ ((sublist (0) ((i + 2 )) (l_up_shifted)) = (app ((sublist (0) ((i + 1 )) (l_up_shifted))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_shifted))))) ” 
  &&  “ ((Zlength ((sublist (0) ((i + 1 )) (l_up_shifted)))) = ((i + 1 ) - 0 )) ”
  &&  emp
).

Definition mpn_lshift_which_implies_wit_2_split_goal_1 := 
forall (n_pre: Z) (up_pre: Z) (l_up_shifted: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : ((i + 1 ) < n_pre)) ,
  ((sublist (0) ((i + 2 )) (l_up_shifted)) = (app ((sublist (0) ((i + 1 )) (l_up_shifted))) ((sublist ((i + 1 )) ((i + 2 )) (l_up_shifted)))))
.

Definition mpn_lshift_which_implies_wit_2_split_goal_2 := 
forall (n_pre: Z) (up_pre: Z) (l_up_shifted: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (0 <= i)) (PreH3 : ((i + 1 ) < n_pre)) ,
  ((Zlength ((sublist (0) ((i + 1 )) (l_up_shifted)))) = ((i + 1 ) - 0 ))
.

Definition mpn_lshift_which_implies_wit_3 := 
(
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : ((i + 1 ) < n_pre)) ,
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
) \/
(
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : ((i + 1 ) < n_pre)) ,
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
|--
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
).

Definition mpn_lshift_which_implies_wit_3_split_goal_spatial := 
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : ((i + 1 ) < n_pre)) ,
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 2 ) )
|--
  (UIntArray.undef_seg up_pre (i + 2 ) ((off_shifted + i ) + 1 ) )
  **  (UIntArray.undef_seg rp_pre (i + 1 ) (i + 2 ) )
.

Definition mpn_lshift_which_implies_wit_4 := 
forall (up_pre: Z) (l_up_shifted: (@list Z)) (rp: Z) (i: Z) (PreH1 : (rp = up_pre)) (PreH2 : (i = 0)) ,
  (UIntArray.seg up_pre 0 1 (sublist (0) (1) (l_up_shifted)) )
|--
  “ (rp = up_pre) ” 
  &&  “ (i = 0) ”
  &&  (UIntArray.seg rp 0 1 (sublist (0) (1) (l_up_shifted)) )
.

Definition mpn_lshift_which_implies_wit_5 := 
(
forall (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (i = 0)) ,
  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
|--
  “ (rp_pre = (up_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (i = 0) ”
  &&  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
) \/
(
forall (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (i = 0)) ,
  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
|--
  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
).

Definition mpn_lshift_which_implies_wit_5_split_goal_spatial := 
forall (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (i: Z) (PreH1 : (rp_pre = (up_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (i = 0)) ,
  (UIntArray.undef_seg up_pre 1 (off_shifted + 1 ) )
|--
  (UIntArray.undef_seg up_pre 1 off_shifted )
  **  (UIntArray.undef_seg rp_pre 0 1 )
.

(*----- Function mpz_mul_2exp -----*)

Definition mpz_mul_2exp_safety_wit_1 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_2 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_3 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <> 0) ”
.

Definition mpz_mul_2exp_safety_wit_4 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_mul_2exp_safety_wit_5 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <> 0) ”
.

Definition mpz_mul_2exp_safety_wit_6 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_mul_2exp_safety_wit_7 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) ”
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) ”
).

Definition mpz_mul_2exp_safety_wit_7_split_goal_1 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ”
.

Definition mpz_mul_2exp_safety_wit_7_split_goal_2 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) ”
.

Definition mpz_mul_2exp_safety_wit_8 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) ”
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) ”
).

Definition mpz_mul_2exp_safety_wit_8_split_goal_1 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ”
.

Definition mpz_mul_2exp_safety_wit_8_split_goal_2 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((INT_MIN) <= ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) ”
.

Definition mpz_mul_2exp_safety_wit_9 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ”
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ”
).

Definition mpz_mul_2exp_safety_wit_9_split_goal_1 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
.

Definition mpz_mul_2exp_safety_wit_9_split_goal_2 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((INT_MIN) <= (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ”
.

Definition mpz_mul_2exp_safety_wit_10 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_11 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (size: Z) (cap: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : (same_sign z_eq size )) (PreH2 : (z_callee__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)))) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_12 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (size: Z) (cap: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : (same_sign z_eq size )) (PreH2 : (z_callee__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)))) (PreH3 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH4 : (retval <> 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> retval_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_13 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (size: Z) (cap: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (same_sign z_eq size )) (PreH3 : (z_callee__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)))) (PreH4 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> retval_2)
|--
  “ False ”
.

Definition mpz_mul_2exp_safety_wit_14 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (size: Z) (cap: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (same_sign z_eq size )) (PreH3 : (z_callee__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)))) (PreH4 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size )) (PreH11 : ((Zabs (size)) <= cap)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |-> retval_2)
|--
  “ False ”
.

Definition mpz_mul_2exp_safety_wit_15 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l_in)) = un)) (PreH18 : (list_within_bound UINT_MOD l_in )) (PreH19 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH20 : ((last (l_in) (1)) >= 1)) (PreH21 : ((Zlength (l_out)) = un)) (PreH22 : (list_within_bound UINT_MOD l_out )) (PreH23 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH24 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH25 : (u__mp_d = rp)) (PreH26 : (rp = u__mp_d)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rn - 1 )) ”
.

Definition mpz_mul_2exp_safety_wit_16 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l_in)) = un)) (PreH18 : (list_within_bound UINT_MOD l_in )) (PreH19 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH20 : ((last (l_in) (1)) >= 1)) (PreH21 : ((Zlength (l_out)) = un)) (PreH22 : (list_within_bound UINT_MOD l_out )) (PreH23 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH24 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH25 : (u__mp_d = rp)) (PreH26 : (rp = u__mp_d)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_mul_2exp_safety_wit_17 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val = 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)) ,
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rn - 1 )) ”
.

Definition mpz_mul_2exp_safety_wit_18 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val <> 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)) ,
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rn - 0 )) ”
.

Definition mpz_mul_2exp_safety_wit_19 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l_in)) = un)) (PreH18 : (list_within_bound UINT_MOD l_in )) (PreH19 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH20 : ((last (l_in) (1)) >= 1)) (PreH21 : ((Zlength (l_out)) = un)) (PreH22 : (list_within_bound UINT_MOD l_out )) (PreH23 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH24 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH25 : (u__mp_d = rp)) (PreH26 : (rp = u__mp_d)) ,
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((( &( "cy" ) )) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_20 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 0 ) <> (INT_MIN)) ”
.

Definition mpz_mul_2exp_safety_wit_21 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = limbs)) (PreH2 : (list_within_bound UINT_MOD l )) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH4 : (cy_val <> 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift > 0)) (PreH16 : (1 <= shift)) (PreH17 : (shift < 32)) (PreH18 : (rn = ((un + limbs ) + 1 ))) (PreH19 : (rn <= INT_MAX)) (PreH20 : ((un + limbs ) <= INT_MAX)) (PreH21 : ((Zlength (l_in)) = un)) (PreH22 : (list_within_bound UINT_MOD l_in )) (PreH23 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH24 : ((last (l_in) (1)) >= 1)) (PreH25 : ((Zlength (l_out)) = un)) (PreH26 : (list_within_bound UINT_MOD l_out )) (PreH27 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH28 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH29 : (u__mp_d = rp)) (PreH30 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_22 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ ((rn - 1 ) <> (INT_MIN)) ”
.

Definition mpz_mul_2exp_safety_wit_23 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = limbs)) (PreH2 : (list_within_bound UINT_MOD l )) (PreH3 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH4 : (cy_val = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift > 0)) (PreH16 : (1 <= shift)) (PreH17 : (shift < 32)) (PreH18 : (rn = ((un + limbs ) + 1 ))) (PreH19 : (rn <= INT_MAX)) (PreH20 : ((un + limbs ) <= INT_MAX)) (PreH21 : ((Zlength (l_in)) = un)) (PreH22 : (list_within_bound UINT_MOD l_in )) (PreH23 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH24 : ((last (l_in) (1)) >= 1)) (PreH25 : ((Zlength (l_out)) = un)) (PreH26 : (list_within_bound UINT_MOD l_out )) (PreH27 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH28 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH29 : (u__mp_d = rp)) (PreH30 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_safety_wit_24 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l_2 )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (rn <> (INT_MIN)) ”
.

Definition mpz_mul_2exp_safety_wit_25 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : ((Zlength (l_2)) = limbs)) (PreH2 : (list_within_bound UINT_MOD l_2 )) (PreH3 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (un = (Zabs (size)))) (PreH10 : (un > 0)) (PreH11 : (limbs = (bits_pre ÷ 32 ))) (PreH12 : (limbs >= 0)) (PreH13 : (shift = (bits_pre % ( 32 ) ))) (PreH14 : (shift = 0)) (PreH15 : (rn = (un + limbs ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l)) = un)) (PreH19 : (list_within_bound UINT_MOD l )) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH21 : ((last (l) (1)) >= 1)) (PreH22 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH23 : (u__mp_d = rp)) (PreH24 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l_2 )
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_mul_2exp_entail_wit_1 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) ,
  (store_Z r_pre z_eq )
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) ,
  (store_Z r_pre z_eq )
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
).

Definition mpz_mul_2exp_entail_wit_2 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (size_2: Z) (cap_2: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (same_sign z_eq size_2 )) (PreH3 : (z_callee__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap_2)))) (PreH4 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Zabs (size_2)))) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size_2 )) (PreH11 : ((Zabs (size_2)) <= cap_2)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size_2)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (u__mp_d: Z)  (u__mp_alloc: Z)  (l: (@list Z))  (cap: Z)  (size: Z) ,
  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval > 0) ” 
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) = (bits_pre ÷ 32 )) ” 
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = (bits_pre % ( 32 ) )) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0) ” 
  &&  “ (1 <= (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) < 32) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) = ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = retval) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap))) ” 
  &&  “ (u__mp_d = retval_2) ” 
  &&  “ (retval_2 = u__mp_d) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full u__mp_d retval l )
  **  (UIntArray.undef_seg u__mp_d retval (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) )
  **  (UIntArray.undef_seg u__mp_d (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (size_2: Z) (cap_2: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : (z_callee__mp_alloc <= INT_MAX)) (PreH2 : (size_2 <= INT_MAX)) (PreH3 : (z_callee__mp_alloc >= INT_MIN)) (PreH4 : (size_2 >= INT_MIN)) (PreH5 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH6 : (same_sign z_eq size_2 )) (PreH7 : (z_callee__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap_2)))) (PreH8 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Zabs (size_2)))) (PreH11 : (r_pre = u_pre)) (PreH12 : (bits_pre >= 0)) (PreH13 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH14 : (same_sign z_eq size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size_2)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (l: (@list Z))  (cap: Z)  (size: Z) ,
  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval > 0) ” 
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) = (bits_pre ÷ 32 )) ” 
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = (bits_pre % ( 32 ) )) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0) ” 
  &&  “ (1 <= (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32))) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) < 32) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = retval) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.full retval_2 retval l )
  **  (UIntArray.undef_seg retval_2 retval (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) )
  **  (UIntArray.undef_seg retval_2 (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 )) (cap)) )
).

Definition mpz_mul_2exp_entail_wit_3 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc_2: Z) (u__mp_d_2: Z) (rp: Z) (l: (@list Z)) (size_2: Z) (cap_2: Z) (l_out_2: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out_2)) = un)) (PreH2 : (list_within_bound UINT_MOD l_out_2 )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out_2)) + (retval * (Z.pow (UINT_MOD) (un)) ) ) = ((list_to_Z (UINT_MOD) (l)) * (Z.pow (2) (shift)) ))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (un = (Zabs (size_2)))) (PreH10 : (un > 0)) (PreH11 : (limbs = (bits_pre ÷ 32 ))) (PreH12 : (limbs >= 0)) (PreH13 : (shift = (bits_pre % ( 32 ) ))) (PreH14 : (shift > 0)) (PreH15 : (1 <= shift)) (PreH16 : (shift < 32)) (PreH17 : (rn = ((un + limbs ) + 1 ))) (PreH18 : (rn <= INT_MAX)) (PreH19 : ((un + limbs ) <= INT_MAX)) (PreH20 : ((Zlength (l)) = un)) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH23 : ((last (l) (1)) >= 1)) (PreH24 : (u__mp_alloc_2 = (Z.max (rn) (cap_2)))) (PreH25 : (u__mp_d_2 = rp)) (PreH26 : (rp = u__mp_d_2)) ,
  (UIntArray.undef_seg u__mp_d_2 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d_2)
  **  (UIntArray.undef_seg u__mp_d_2 (un + limbs ) (Z.max (rn) (cap_2)) )
|--
  EX (u__mp_d: Z)  (u__mp_alloc: Z)  (l_out: (@list Z))  (l_in: (@list Z))  (cap: Z)  (size: Z) ,
  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_in)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_in ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l_in) (1)) >= 1) ” 
  &&  “ ((Zlength (l_out)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (retval * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc_2: Z) (u__mp_d_2: Z) (rp: Z) (l: (@list Z)) (size_2: Z) (cap_2: Z) (l_out_2: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out_2)) = un)) (PreH2 : (list_within_bound UINT_MOD l_out_2 )) (PreH3 : (((list_to_Z (UINT_MOD) (l_out_2)) + (retval * (Z.pow (UINT_MOD) (un)) ) ) = ((list_to_Z (UINT_MOD) (l)) * (Z.pow (2) (shift)) ))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size_2 )) (PreH8 : ((Zabs (size_2)) <= cap_2)) (PreH9 : (un = (Zabs (size_2)))) (PreH10 : (un > 0)) (PreH11 : (limbs = (bits_pre ÷ 32 ))) (PreH12 : (limbs >= 0)) (PreH13 : (shift = (bits_pre % ( 32 ) ))) (PreH14 : (shift > 0)) (PreH15 : (1 <= shift)) (PreH16 : (shift < 32)) (PreH17 : (rn = ((un + limbs ) + 1 ))) (PreH18 : (rn <= INT_MAX)) (PreH19 : ((un + limbs ) <= INT_MAX)) (PreH20 : ((Zlength (l)) = un)) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH23 : ((last (l) (1)) >= 1)) (PreH24 : (u__mp_alloc_2 = (Z.max (rn) (cap_2)))) (PreH25 : (u__mp_d_2 = rp)) (PreH26 : (rp = u__mp_d_2)) ,
  (UIntArray.undef_seg u__mp_d_2 0 limbs )
  **  (UIntArray.undef_seg u__mp_d_2 (un + limbs ) (Z.max (rn) (cap_2)) )
|--
  EX (l_in: (@list Z))  (cap: Z) ,
  “ (u__mp_d_2 = rp) ” 
  &&  “ (u__mp_alloc_2 = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d_2 = rp) ” 
  &&  “ (u__mp_alloc_2 = (Z.max (rn) (cap))) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ” 
  &&  “ (un = (Zabs (size_2))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_in)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_in ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l_in) (1)) >= 1) ” 
  &&  “ ((Zlength (l_out_2)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_out_2 ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out_2)) + (retval * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
).

Definition mpz_mul_2exp_entail_wit_4 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (size_2: Z) (cap_2: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (same_sign z_eq size_2 )) (PreH3 : (z_callee__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap_2)))) (PreH4 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH5 : (retval <> 0)) (PreH6 : (retval = (Zabs (size_2)))) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size_2 )) (PreH11 : ((Zabs (size_2)) <= cap_2)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size_2)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (u__mp_d: Z)  (u__mp_alloc: Z)  (l: (@list Z))  (cap: Z)  (size: Z) ,
  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval > 0) ” 
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) = (bits_pre ÷ 32 )) ” 
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = (bits_pre % ( 32 ) )) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = 0) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) = (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ” 
  &&  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = retval) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap))) ” 
  &&  “ (u__mp_d = retval_2) ” 
  &&  “ (retval_2 = u__mp_d) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full u__mp_d retval l )
  **  (UIntArray.undef_seg u__mp_d retval (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) )
  **  (UIntArray.undef_seg u__mp_d (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (size_2: Z) (cap_2: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : (z_callee__mp_alloc <= INT_MAX)) (PreH2 : (size_2 <= INT_MAX)) (PreH3 : (z_callee__mp_alloc >= INT_MIN)) (PreH4 : (size_2 >= INT_MIN)) (PreH5 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH6 : (same_sign z_eq size_2 )) (PreH7 : (z_callee__mp_alloc = (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap_2)))) (PreH8 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH9 : (retval <> 0)) (PreH10 : (retval = (Zabs (size_2)))) (PreH11 : (r_pre = u_pre)) (PreH12 : (bits_pre >= 0)) (PreH13 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH14 : (same_sign z_eq size_2 )) (PreH15 : ((Zabs (size_2)) <= cap_2)) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq)) (Zabs (size_2)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size_2)) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap_2)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (l: (@list Z))  (cap: Z)  (size: Z) ,
  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (retval > 0) ” 
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) = (bits_pre ÷ 32 )) ” 
  &&  “ ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= 0) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = (bits_pre % ( 32 ) )) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) = 0) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) = (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) )) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ” 
  &&  “ ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = retval) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.full retval_2 retval l )
  **  (UIntArray.undef_seg retval_2 retval (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) )
  **  (UIntArray.undef_seg retval_2 (retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) (Z.max (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 )) (cap)) )
).

Definition mpz_mul_2exp_entail_wit_5 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc_2: Z) (u__mp_d_2: Z) (rp: Z) (l_2: (@list Z)) (size_2: Z) (cap_2: Z) (PreH1 : ((rp + (limbs * sizeof(UINT))) = (u__mp_d_2 + (limbs * sizeof(UINT))))) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (un = (Zabs (size_2)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift = 0)) (PreH13 : (rn = (un + limbs ))) (PreH14 : (rn <= INT_MAX)) (PreH15 : ((un + limbs ) <= INT_MAX)) (PreH16 : ((Zlength (l_2)) = un)) (PreH17 : (list_within_bound UINT_MOD l_2 )) (PreH18 : ((list_to_Z (UINT_MOD) (l_2)) = (Zabs (z_eq)))) (PreH19 : ((last (l_2) (1)) >= 1)) (PreH20 : (u__mp_alloc_2 = (Z.max (rn) (cap_2)))) (PreH21 : (u__mp_d_2 = rp)) (PreH22 : (rp = u__mp_d_2)) ,
  (UIntArray.undef_seg u__mp_d_2 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l_2)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc_2)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d_2)
  **  (UIntArray.undef_seg u__mp_d_2 (un + limbs ) (Z.max (rn) (cap_2)) )
|--
  EX (u__mp_d: Z)  (u__mp_alloc: Z)  (l: (@list Z))  (cap: Z)  (size: Z) ,
  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift = 0) ” 
  &&  “ (rn = (un + limbs )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc_2: Z) (u__mp_d_2: Z) (rp: Z) (l_2: (@list Z)) (size_2: Z) (cap_2: Z) (PreH1 : ((rp + (limbs * sizeof(UINT))) = (u__mp_d_2 + (limbs * sizeof(UINT))))) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size_2 )) (PreH6 : ((Zabs (size_2)) <= cap_2)) (PreH7 : (un = (Zabs (size_2)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift = 0)) (PreH13 : (rn = (un + limbs ))) (PreH14 : (rn <= INT_MAX)) (PreH15 : ((un + limbs ) <= INT_MAX)) (PreH16 : ((Zlength (l_2)) = un)) (PreH17 : (list_within_bound UINT_MOD l_2 )) (PreH18 : ((list_to_Z (UINT_MOD) (l_2)) = (Zabs (z_eq)))) (PreH19 : ((last (l_2) (1)) >= 1)) (PreH20 : (u__mp_alloc_2 = (Z.max (rn) (cap_2)))) (PreH21 : (u__mp_d_2 = rp)) (PreH22 : (rp = u__mp_d_2)) ,
  (UIntArray.undef_seg u__mp_d_2 0 limbs )
  **  (UIntArray.undef_seg u__mp_d_2 (un + limbs ) (Z.max (rn) (cap_2)) )
|--
  EX (l: (@list Z))  (cap: Z) ,
  “ ((sublist (0) (un) (l_2)) = (sublist (0) (un) (l))) ” 
  &&  “ (u__mp_d_2 = rp) ” 
  &&  “ (u__mp_alloc_2 = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d_2 = rp) ” 
  &&  “ (u__mp_alloc_2 = (Z.max (rn) (cap))) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size_2 ) ” 
  &&  “ ((Zabs (size_2)) <= cap) ” 
  &&  “ (un = (Zabs (size_2))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift = 0) ” 
  &&  “ (rn = (un + limbs )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
).

Definition mpz_mul_2exp_return_wit_1 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (cap >= INT_MIN)) (PreH3 : (retval = 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  EX (cap_2: Z)  (ptr_2: Z) ,
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) 0 ) ” 
  &&  “ ((Zabs (0)) <= cap_2) ” 
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs (0)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs (0)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_2 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-(rn - 0 )))
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (cy_val <= UINT_MAX)) (PreH2 : (cy_val >= 0)) (PreH3 : (u__mp_alloc <= INT_MAX)) (PreH4 : (u__mp_alloc >= INT_MIN)) (PreH5 : (size < 0)) (PreH6 : ((Zlength (l)) = limbs)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH9 : (cy_val <> 0)) (PreH10 : (r_pre = u_pre)) (PreH11 : (bits_pre >= 0)) (PreH12 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH13 : (same_sign z_eq size )) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (un = (Zabs (size)))) (PreH16 : (un > 0)) (PreH17 : (limbs = (bits_pre ÷ 32 ))) (PreH18 : (limbs >= 0)) (PreH19 : (shift = (bits_pre % ( 32 ) ))) (PreH20 : (shift > 0)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (rn = ((un + limbs ) + 1 ))) (PreH24 : (rn <= INT_MAX)) (PreH25 : ((un + limbs ) <= INT_MAX)) (PreH26 : ((Zlength (l_in)) = un)) (PreH27 : (list_within_bound UINT_MOD l_in )) (PreH28 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH29 : ((last (l_in) (1)) >= 1)) (PreH30 : ((Zlength (l_out)) = un)) (PreH31 : (list_within_bound UINT_MOD l_out )) (PreH32 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH33 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH34 : (u__mp_d = rp)) (PreH35 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (-(rn - 0 )) ) ” 
  &&  “ ((Zabs ((-(rn - 0 )))) <= cap_2) ” 
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((-(rn - 0 )))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((-(rn - 0 )))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_3 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (rn - 0 ))
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (cy_val <= UINT_MAX)) (PreH2 : (cy_val >= 0)) (PreH3 : (u__mp_alloc <= INT_MAX)) (PreH4 : (u__mp_alloc >= INT_MIN)) (PreH5 : (size >= 0)) (PreH6 : ((Zlength (l)) = limbs)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH9 : (cy_val <> 0)) (PreH10 : (r_pre = u_pre)) (PreH11 : (bits_pre >= 0)) (PreH12 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH13 : (same_sign z_eq size )) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (un = (Zabs (size)))) (PreH16 : (un > 0)) (PreH17 : (limbs = (bits_pre ÷ 32 ))) (PreH18 : (limbs >= 0)) (PreH19 : (shift = (bits_pre % ( 32 ) ))) (PreH20 : (shift > 0)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (rn = ((un + limbs ) + 1 ))) (PreH24 : (rn <= INT_MAX)) (PreH25 : ((un + limbs ) <= INT_MAX)) (PreH26 : ((Zlength (l_in)) = un)) (PreH27 : (list_within_bound UINT_MOD l_in )) (PreH28 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH29 : ((last (l_in) (1)) >= 1)) (PreH30 : ((Zlength (l_out)) = un)) (PreH31 : (list_within_bound UINT_MOD l_out )) (PreH32 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH33 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH34 : (u__mp_d = rp)) (PreH35 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (rn - 0 ) ) ” 
  &&  “ ((Zabs ((rn - 0 ))) <= cap_2) ” 
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((rn - 0 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((rn - 0 ))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_4 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-(rn - 1 )))
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (cy_val <= UINT_MAX)) (PreH2 : (cy_val >= 0)) (PreH3 : (u__mp_alloc <= INT_MAX)) (PreH4 : (u__mp_alloc >= INT_MIN)) (PreH5 : (size < 0)) (PreH6 : ((Zlength (l)) = limbs)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH9 : (cy_val = 0)) (PreH10 : (r_pre = u_pre)) (PreH11 : (bits_pre >= 0)) (PreH12 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH13 : (same_sign z_eq size )) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (un = (Zabs (size)))) (PreH16 : (un > 0)) (PreH17 : (limbs = (bits_pre ÷ 32 ))) (PreH18 : (limbs >= 0)) (PreH19 : (shift = (bits_pre % ( 32 ) ))) (PreH20 : (shift > 0)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (rn = ((un + limbs ) + 1 ))) (PreH24 : (rn <= INT_MAX)) (PreH25 : ((un + limbs ) <= INT_MAX)) (PreH26 : ((Zlength (l_in)) = un)) (PreH27 : (list_within_bound UINT_MOD l_in )) (PreH28 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH29 : ((last (l_in) (1)) >= 1)) (PreH30 : ((Zlength (l_out)) = un)) (PreH31 : (list_within_bound UINT_MOD l_out )) (PreH32 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH33 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH34 : (u__mp_d = rp)) (PreH35 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (-(rn - 1 )) ) ” 
  &&  “ ((Zabs ((-(rn - 1 )))) <= cap_2) ” 
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((-(rn - 1 )))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((-(rn - 1 )))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_5 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (rn - 1 ))
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (cy_val <= UINT_MAX)) (PreH2 : (cy_val >= 0)) (PreH3 : (u__mp_alloc <= INT_MAX)) (PreH4 : (u__mp_alloc >= INT_MIN)) (PreH5 : (size >= 0)) (PreH6 : ((Zlength (l)) = limbs)) (PreH7 : (list_within_bound UINT_MOD l )) (PreH8 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH9 : (cy_val = 0)) (PreH10 : (r_pre = u_pre)) (PreH11 : (bits_pre >= 0)) (PreH12 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH13 : (same_sign z_eq size )) (PreH14 : ((Zabs (size)) <= cap)) (PreH15 : (un = (Zabs (size)))) (PreH16 : (un > 0)) (PreH17 : (limbs = (bits_pre ÷ 32 ))) (PreH18 : (limbs >= 0)) (PreH19 : (shift = (bits_pre % ( 32 ) ))) (PreH20 : (shift > 0)) (PreH21 : (1 <= shift)) (PreH22 : (shift < 32)) (PreH23 : (rn = ((un + limbs ) + 1 ))) (PreH24 : (rn <= INT_MAX)) (PreH25 : ((un + limbs ) <= INT_MAX)) (PreH26 : ((Zlength (l_in)) = un)) (PreH27 : (list_within_bound UINT_MOD l_in )) (PreH28 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH29 : ((last (l_in) (1)) >= 1)) (PreH30 : ((Zlength (l_out)) = un)) (PreH31 : (list_within_bound UINT_MOD l_out )) (PreH32 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH33 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH34 : (u__mp_d = rp)) (PreH35 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (rn - 1 ) ) ” 
  &&  “ ((Zabs ((rn - 1 ))) <= cap_2) ” 
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((rn - 1 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((rn - 1 ))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_6 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (-rn))
  **  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (size < 0)) (PreH4 : ((Zlength (l_2)) = limbs)) (PreH5 : (list_within_bound UINT_MOD l_2 )) (PreH6 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size )) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (un = (Zabs (size)))) (PreH13 : (un > 0)) (PreH14 : (limbs = (bits_pre ÷ 32 ))) (PreH15 : (limbs >= 0)) (PreH16 : (shift = (bits_pre % ( 32 ) ))) (PreH17 : (shift = 0)) (PreH18 : (rn = (un + limbs ))) (PreH19 : (rn <= INT_MAX)) (PreH20 : ((un + limbs ) <= INT_MAX)) (PreH21 : ((Zlength (l)) = un)) (PreH22 : (list_within_bound UINT_MOD l )) (PreH23 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH24 : ((last (l) (1)) >= 1)) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) (-rn) ) ” 
  &&  “ ((Zabs ((-rn))) <= cap_2) ” 
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((-rn))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs ((-rn))) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_return_wit_7 := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)) ,
  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> rn)
  **  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (z_eq * (Z.pow (2) (bits_pre)) ) )
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (size >= 0)) (PreH4 : ((Zlength (l_2)) = limbs)) (PreH5 : (list_within_bound UINT_MOD l_2 )) (PreH6 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH7 : (r_pre = u_pre)) (PreH8 : (bits_pre >= 0)) (PreH9 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH10 : (same_sign z_eq size )) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (un = (Zabs (size)))) (PreH13 : (un > 0)) (PreH14 : (limbs = (bits_pre ÷ 32 ))) (PreH15 : (limbs >= 0)) (PreH16 : (shift = (bits_pre % ( 32 ) ))) (PreH17 : (shift = 0)) (PreH18 : (rn = (un + limbs ))) (PreH19 : (rn <= INT_MAX)) (PreH20 : ((un + limbs ) <= INT_MAX)) (PreH21 : ((Zlength (l)) = un)) (PreH22 : (list_within_bound UINT_MOD l )) (PreH23 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH24 : ((last (l) (1)) >= 1)) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (z_eq * (Z.pow (2) (bits_pre)) ) rn ) ” 
  &&  “ ((Zabs (rn)) <= cap_2) ” 
  &&  “ (r_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs (rn)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((z_eq * (Z.pow (2) (bits_pre)) ))) (Zabs (rn)) )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_mul_2exp_partial_solve_wit_1_pure := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_mul_2exp_partial_solve_wit_1_pure_split_goal_1 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (cap >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |->_)
  **  ((( &( "rn" ) )) # Int  |->_)
  **  ((( &( "limbs" ) )) # Int  |->_)
  **  ((( &( "shift" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_mul_2exp_partial_solve_wit_1_aux := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_mul_2exp_partial_solve_wit_1 := mpz_mul_2exp_partial_solve_wit_1_pure -> mpz_mul_2exp_partial_solve_wit_1_aux.

Definition mpz_mul_2exp_partial_solve_wit_2 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (r_pre = u_pre)) (PreH4 : (bits_pre >= 0)) (PreH5 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH6 : (same_sign z_eq size )) (PreH7 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (retval = 0) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_mul_2exp_partial_solve_wit_3_pure := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (cap >= 0) ”
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH6 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH11 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Zabs (size)))) (PreH16 : (r_pre = u_pre)) (PreH17 : (bits_pre >= 0)) (PreH18 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH19 : (same_sign z_eq size )) (PreH20 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ”
).

Definition mpz_mul_2exp_partial_solve_wit_3_pure_split_goal_1 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH6 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH11 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Zabs (size)))) (PreH16 : (r_pre = u_pre)) (PreH17 : (bits_pre >= 0)) (PreH18 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH19 : (same_sign z_eq size )) (PreH20 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_3_pure_split_goal_2 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH6 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH11 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Zabs (size)))) (PreH16 : (r_pre = u_pre)) (PreH17 : (bits_pre >= 0)) (PreH18 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH19 : (same_sign z_eq size )) (PreH20 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_3_pure_split_goal_3 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH6 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH11 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Zabs (size)))) (PreH16 : (r_pre = u_pre)) (PreH17 : (bits_pre >= 0)) (PreH18 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH19 : (same_sign z_eq size )) (PreH20 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_3_aux := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) <= INT_MAX) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 0 ) >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_mul_2exp_partial_solve_wit_3 := mpz_mul_2exp_partial_solve_wit_3_pure -> mpz_mul_2exp_partial_solve_wit_3_aux.

Definition mpz_mul_2exp_partial_solve_wit_4_pure := 
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (cap >= 0) ”
) \/
(
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH6 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH11 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Zabs (size)))) (PreH16 : (r_pre = u_pre)) (PreH17 : (bits_pre >= 0)) (PreH18 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH19 : (same_sign z_eq size )) (PreH20 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ”
).

Definition mpz_mul_2exp_partial_solve_wit_4_pure_split_goal_1 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH6 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH11 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Zabs (size)))) (PreH16 : (r_pre = u_pre)) (PreH17 : (bits_pre >= 0)) (PreH18 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH19 : (same_sign z_eq size )) (PreH20 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_4_pure_split_goal_2 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH6 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH11 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Zabs (size)))) (PreH16 : (r_pre = u_pre)) (PreH17 : (bits_pre >= 0)) (PreH18 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH19 : (same_sign z_eq size )) (PreH20 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_4_pure_split_goal_3 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) <= UINT_MAX)) (PreH2 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) >= 0)) (PreH3 : (cap <= INT_MAX)) (PreH4 : (size <= INT_MAX)) (PreH5 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH6 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX)) (PreH7 : (retval <= INT_MAX)) (PreH8 : (cap >= INT_MIN)) (PreH9 : (size >= INT_MIN)) (PreH10 : ((signed_last_nbits ((bits_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH11 : (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH14 : (retval <> 0)) (PreH15 : (retval = (Zabs (size)))) (PreH16 : (r_pre = u_pre)) (PreH17 : (bits_pre >= 0)) (PreH18 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH19 : (same_sign z_eq size )) (PreH20 : ((Zabs (size)) <= cap)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> retval)
  **  ((( &( "rn" ) )) # Int  |-> ((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ))
  **  ((( &( "limbs" ) )) # Int  |-> (signed_last_nbits ((bits_pre ÷ 32 )) (32)))
  **  ((( &( "shift" ) )) # UInt  |-> (unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)))
  **  ((( &( "rp" ) )) # Ptr  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ”
.

Definition mpz_mul_2exp_partial_solve_wit_4_aux := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0)) (PreH2 : (retval <> 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (r_pre = u_pre)) (PreH5 : (bits_pre >= 0)) (PreH6 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH7 : (same_sign z_eq size )) (PreH8 : ((Zabs (size)) <= cap)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ” 
  &&  “ (((retval + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((((Zabs (size)) + (signed_last_nbits ((bits_pre ÷ 32 )) (32)) ) + 1 ) >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (cap >= 0) ” 
  &&  “ ((unsigned_last_nbits ((bits_pre % ( 32 ) )) (32)) > 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_mul_2exp_partial_solve_wit_4 := mpz_mul_2exp_partial_solve_wit_4_pure -> mpz_mul_2exp_partial_solve_wit_4_aux.

Definition mpz_mul_2exp_partial_solve_wit_5_pure := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l)) = un)) (PreH18 : (list_within_bound UINT_MOD l )) (PreH19 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH20 : ((last (l) (1)) >= 1)) (PreH21 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH22 : (u__mp_d = rp)) (PreH23 : (rp = u__mp_d)) ,
  ((( &( "cy" ) )) # UInt  |->_)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (un > 0) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((rp + (limbs * sizeof(UINT))) = (u__mp_d + (limbs * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
.

Definition mpz_mul_2exp_partial_solve_wit_5_aux := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l)) = un)) (PreH18 : (list_within_bound UINT_MOD l )) (PreH19 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH20 : ((last (l) (1)) >= 1)) (PreH21 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH22 : (u__mp_d = rp)) (PreH23 : (rp = u__mp_d)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (un > 0) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ ((rp + (limbs * sizeof(UINT))) = (u__mp_d + (limbs * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_5 := mpz_mul_2exp_partial_solve_wit_5_pure -> mpz_mul_2exp_partial_solve_wit_5_aux.

Definition mpz_mul_2exp_partial_solve_wit_6 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift > 0)) (PreH12 : (1 <= shift)) (PreH13 : (shift < 32)) (PreH14 : (rn = ((un + limbs ) + 1 ))) (PreH15 : (rn <= INT_MAX)) (PreH16 : ((un + limbs ) <= INT_MAX)) (PreH17 : ((Zlength (l_in)) = un)) (PreH18 : (list_within_bound UINT_MOD l_in )) (PreH19 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH20 : ((last (l_in) (1)) >= 1)) (PreH21 : ((Zlength (l_out)) = un)) (PreH22 : (list_within_bound UINT_MOD l_out )) (PreH23 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH24 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH25 : (u__mp_d = rp)) (PreH26 : (rp = u__mp_d)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp (un + limbs ) rn )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_in)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_in ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l_in) (1)) >= 1) ” 
  &&  “ ((Zlength (l_out)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.undef_missing_i rp (rn - 1 ) (un + limbs ) rn )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_7_pure := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift = 0)) (PreH12 : (rn = (un + limbs ))) (PreH13 : (rn <= INT_MAX)) (PreH14 : ((un + limbs ) <= INT_MAX)) (PreH15 : ((Zlength (l)) = un)) (PreH16 : (list_within_bound UINT_MOD l )) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH18 : ((last (l) (1)) >= 1)) (PreH19 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH20 : (u__mp_d = rp)) (PreH21 : (rp = u__mp_d)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (un >= 0) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((rp + (limbs * sizeof(UINT))) = (u__mp_d + (limbs * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ”
.

Definition mpz_mul_2exp_partial_solve_wit_7_aux := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (size: Z) (cap: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift = 0)) (PreH12 : (rn = (un + limbs ))) (PreH13 : (rn <= INT_MAX)) (PreH14 : ((un + limbs ) <= INT_MAX)) (PreH15 : ((Zlength (l)) = un)) (PreH16 : (list_within_bound UINT_MOD l )) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH18 : ((last (l) (1)) >= 1)) (PreH19 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH20 : (u__mp_d = rp)) (PreH21 : (rp = u__mp_d)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (un >= 0) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((rp + (limbs * sizeof(UINT))) = (u__mp_d + (limbs * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift = 0) ” 
  &&  “ (rn = (un + limbs )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.full u__mp_d un l )
  **  (UIntArray.undef_seg u__mp_d un (un + limbs ) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg u__mp_d (un + limbs ) (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_7 := mpz_mul_2exp_partial_solve_wit_7_pure -> mpz_mul_2exp_partial_solve_wit_7_aux.

Definition mpz_mul_2exp_partial_solve_wit_8_pure := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val <> 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)) ,
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ” 
  &&  “ (limbs <= INT_MAX) ”
.

Definition mpz_mul_2exp_partial_solve_wit_8_aux := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val <> 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)) ,
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ” 
  &&  “ (limbs <= INT_MAX) ” 
  &&  “ (cy_val <> 0) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_in)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_in ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l_in) (1)) >= 1) ” 
  &&  “ ((Zlength (l_out)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_8 := mpz_mul_2exp_partial_solve_wit_8_pure -> mpz_mul_2exp_partial_solve_wit_8_aux.

Definition mpz_mul_2exp_partial_solve_wit_9_pure := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val = 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)) ,
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> (rn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ” 
  &&  “ (limbs <= INT_MAX) ”
.

Definition mpz_mul_2exp_partial_solve_wit_9_aux := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (cy_val = 0)) (PreH2 : (r_pre = u_pre)) (PreH3 : (bits_pre >= 0)) (PreH4 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH5 : (same_sign z_eq size )) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (un = (Zabs (size)))) (PreH8 : (un > 0)) (PreH9 : (limbs = (bits_pre ÷ 32 ))) (PreH10 : (limbs >= 0)) (PreH11 : (shift = (bits_pre % ( 32 ) ))) (PreH12 : (shift > 0)) (PreH13 : (1 <= shift)) (PreH14 : (shift < 32)) (PreH15 : (rn = ((un + limbs ) + 1 ))) (PreH16 : (rn <= INT_MAX)) (PreH17 : ((un + limbs ) <= INT_MAX)) (PreH18 : ((Zlength (l_in)) = un)) (PreH19 : (list_within_bound UINT_MOD l_in )) (PreH20 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH21 : ((last (l_in) (1)) >= 1)) (PreH22 : ((Zlength (l_out)) = un)) (PreH23 : (list_within_bound UINT_MOD l_out )) (PreH24 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH25 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH26 : (u__mp_d = rp)) (PreH27 : (rp = u__mp_d)) ,
  (UIntArray.undef_seg rp ((un + limbs ) + 1 ) rn )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ” 
  &&  “ (limbs <= INT_MAX) ” 
  &&  “ (cy_val = 0) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_in)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_in ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l_in) (1)) >= 1) ” 
  &&  “ ((Zlength (l_out)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_9 := mpz_mul_2exp_partial_solve_wit_9_pure -> mpz_mul_2exp_partial_solve_wit_9_aux.

Definition mpz_mul_2exp_partial_solve_wit_10_pure := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift = 0)) (PreH12 : (rn = (un + limbs ))) (PreH13 : (rn <= INT_MAX)) (PreH14 : ((un + limbs ) <= INT_MAX)) (PreH15 : ((Zlength (l)) = un)) (PreH16 : (list_within_bound UINT_MOD l )) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH18 : ((last (l) (1)) >= 1)) (PreH19 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH20 : (u__mp_d = rp)) (PreH21 : (rp = u__mp_d)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "bits" ) )) # UInt64  |-> bits_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "limbs" ) )) # Int  |-> limbs)
  **  ((( &( "shift" ) )) # UInt  |-> shift)
  **  ((( &( "rn" ) )) # Int  |-> rn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ” 
  &&  “ (limbs <= INT_MAX) ”
.

Definition mpz_mul_2exp_partial_solve_wit_10_aux := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (bits_pre >= 0)) (PreH3 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH4 : (same_sign z_eq size )) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (un = (Zabs (size)))) (PreH7 : (un > 0)) (PreH8 : (limbs = (bits_pre ÷ 32 ))) (PreH9 : (limbs >= 0)) (PreH10 : (shift = (bits_pre % ( 32 ) ))) (PreH11 : (shift = 0)) (PreH12 : (rn = (un + limbs ))) (PreH13 : (rn <= INT_MAX)) (PreH14 : ((un + limbs ) <= INT_MAX)) (PreH15 : ((Zlength (l)) = un)) (PreH16 : (list_within_bound UINT_MOD l )) (PreH17 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH18 : ((last (l) (1)) >= 1)) (PreH19 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH20 : (u__mp_d = rp)) (PreH21 : (rp = u__mp_d)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg rp 0 limbs )
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (limbs >= 0) ” 
  &&  “ (limbs <= INT_MAX) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift = 0) ” 
  &&  “ (rn = (un + limbs )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  (UIntArray.undef_seg rp 0 limbs )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_10 := mpz_mul_2exp_partial_solve_wit_10_pure -> mpz_mul_2exp_partial_solve_wit_10_aux.

Definition mpz_mul_2exp_partial_solve_wit_11 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (size < 0) ” 
  &&  “ ((Zlength (l)) = limbs) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ” 
  &&  “ (cy_val <> 0) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_in)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_in ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l_in) (1)) >= 1) ” 
  &&  “ ((Zlength (l_out)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_12 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val <> 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (size >= 0) ” 
  &&  “ ((Zlength (l)) = limbs) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ” 
  &&  “ (cy_val <> 0) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_in)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_in ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l_in) (1)) >= 1) ” 
  &&  “ ((Zlength (l_out)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_13 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (size < 0) ” 
  &&  “ ((Zlength (l)) = limbs) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ” 
  &&  “ (cy_val = 0) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_in)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_in ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l_in) (1)) >= 1) ” 
  &&  “ ((Zlength (l_out)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_14 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l_in: (@list Z)) (l_out: (@list Z)) (size: Z) (cap: Z) (cy_val: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l )) (PreH4 : ((list_to_Z (UINT_MOD) (l)) = 0)) (PreH5 : (cy_val = 0)) (PreH6 : (r_pre = u_pre)) (PreH7 : (bits_pre >= 0)) (PreH8 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH9 : (same_sign z_eq size )) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (un = (Zabs (size)))) (PreH12 : (un > 0)) (PreH13 : (limbs = (bits_pre ÷ 32 ))) (PreH14 : (limbs >= 0)) (PreH15 : (shift = (bits_pre % ( 32 ) ))) (PreH16 : (shift > 0)) (PreH17 : (1 <= shift)) (PreH18 : (shift < 32)) (PreH19 : (rn = ((un + limbs ) + 1 ))) (PreH20 : (rn <= INT_MAX)) (PreH21 : ((un + limbs ) <= INT_MAX)) (PreH22 : ((Zlength (l_in)) = un)) (PreH23 : (list_within_bound UINT_MOD l_in )) (PreH24 : ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq)))) (PreH25 : ((last (l_in) (1)) >= 1)) (PreH26 : ((Zlength (l_out)) = un)) (PreH27 : (list_within_bound UINT_MOD l_out )) (PreH28 : (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) ))) (PreH29 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH30 : (u__mp_d = rp)) (PreH31 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
|--
  “ (size >= 0) ” 
  &&  “ ((Zlength (l)) = limbs) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = 0) ” 
  &&  “ (cy_val = 0) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift > 0) ” 
  &&  “ (1 <= shift) ” 
  &&  “ (shift < 32) ” 
  &&  “ (rn = ((un + limbs ) + 1 )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l_in)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_in ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_in)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l_in) (1)) >= 1) ” 
  &&  “ ((Zlength (l_out)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (((list_to_Z (UINT_MOD) (l_out)) + (cy_val * (Z.pow (UINT_MOD) (un)) ) ) = ((Zabs (z_eq)) * (Z.pow (2) (shift)) )) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l )
  **  (((rp + ((rn - 1 ) * sizeof(UINT)))) # UInt  |-> cy_val)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un l_out )
  **  (UIntArray.undef_seg rp rn (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_15 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size < 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (size < 0) ” 
  &&  “ ((Zlength (l_2)) = limbs) ” 
  &&  “ (list_within_bound UINT_MOD l_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_2)) = 0) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift = 0) ” 
  &&  “ (rn = (un + limbs )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
.

Definition mpz_mul_2exp_partial_solve_wit_16 := 
forall (bits_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (l: (@list Z)) (size: Z) (cap: Z) (un: Z) (limbs: Z) (shift: Z) (rn: Z) (u__mp_alloc: Z) (u__mp_d: Z) (rp: Z) (l_2: (@list Z)) (PreH1 : (size >= 0)) (PreH2 : ((Zlength (l_2)) = limbs)) (PreH3 : (list_within_bound UINT_MOD l_2 )) (PreH4 : ((list_to_Z (UINT_MOD) (l_2)) = 0)) (PreH5 : (r_pre = u_pre)) (PreH6 : (bits_pre >= 0)) (PreH7 : (mpz_mul_2exp_fits z_eq bits_pre )) (PreH8 : (same_sign z_eq size )) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (un = (Zabs (size)))) (PreH11 : (un > 0)) (PreH12 : (limbs = (bits_pre ÷ 32 ))) (PreH13 : (limbs >= 0)) (PreH14 : (shift = (bits_pre % ( 32 ) ))) (PreH15 : (shift = 0)) (PreH16 : (rn = (un + limbs ))) (PreH17 : (rn <= INT_MAX)) (PreH18 : ((un + limbs ) <= INT_MAX)) (PreH19 : ((Zlength (l)) = un)) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq)))) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_alloc = (Z.max (rn) (cap)))) (PreH24 : (u__mp_d = rp)) (PreH25 : (rp = u__mp_d)) ,
  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
|--
  “ (size >= 0) ” 
  &&  “ ((Zlength (l_2)) = limbs) ” 
  &&  “ (list_within_bound UINT_MOD l_2 ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l_2)) = 0) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (bits_pre >= 0) ” 
  &&  “ (mpz_mul_2exp_fits z_eq bits_pre ) ” 
  &&  “ (same_sign z_eq size ) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (un = (Zabs (size))) ” 
  &&  “ (un > 0) ” 
  &&  “ (limbs = (bits_pre ÷ 32 )) ” 
  &&  “ (limbs >= 0) ” 
  &&  “ (shift = (bits_pre % ( 32 ) )) ” 
  &&  “ (shift = 0) ” 
  &&  “ (rn = (un + limbs )) ” 
  &&  “ (rn <= INT_MAX) ” 
  &&  “ ((un + limbs ) <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = un) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq))) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_alloc = (Z.max (rn) (cap))) ” 
  &&  “ (u__mp_d = rp) ” 
  &&  “ (rp = u__mp_d) ”
  &&  ((&((r_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.full rp limbs l_2 )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.seg (rp + (limbs * sizeof(UINT))) 0 un (sublist (0) (un) (l)) )
  **  (UIntArray.undef_seg rp (un + limbs ) (Z.max (rn) (cap)) )
.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_copyd_safety_wit_1 : mpn_copyd_safety_wit_1.
Axiom proof_of_mpn_copyd_safety_wit_2_off_zero : mpn_copyd_safety_wit_2_off_zero.
Axiom proof_of_mpn_copyd_safety_wit_3_off_pos : mpn_copyd_safety_wit_3_off_pos.
Axiom proof_of_mpn_copyd_safety_wit_4_off_zero : mpn_copyd_safety_wit_4_off_zero.
Axiom proof_of_mpn_copyd_safety_wit_5_off_pos : mpn_copyd_safety_wit_5_off_pos.
Axiom proof_of_mpn_copyd_safety_wit_6_off_zero : mpn_copyd_safety_wit_6_off_zero.
Axiom proof_of_mpn_copyd_safety_wit_7_off_pos : mpn_copyd_safety_wit_7_off_pos.
Axiom proof_of_mpn_copyd_entail_wit_1_off_zero : mpn_copyd_entail_wit_1_off_zero.
Axiom proof_of_mpn_copyd_entail_wit_2_off_pos : mpn_copyd_entail_wit_2_off_pos.
Axiom proof_of_mpn_copyd_entail_wit_3_off_zero : mpn_copyd_entail_wit_3_off_zero.
Axiom proof_of_mpn_copyd_entail_wit_4_off_pos : mpn_copyd_entail_wit_4_off_pos.
Axiom proof_of_mpn_copyd_entail_wit_5_off_pos : mpn_copyd_entail_wit_5_off_pos.
Axiom proof_of_mpn_copyd_entail_wit_6_off_zero : mpn_copyd_entail_wit_6_off_zero.
Axiom proof_of_mpn_copyd_entail_wit_7_off_pos : mpn_copyd_entail_wit_7_off_pos.
Axiom proof_of_mpn_copyd_return_wit_1_off_zero : mpn_copyd_return_wit_1_off_zero.
Axiom proof_of_mpn_copyd_return_wit_2_off_pos : mpn_copyd_return_wit_2_off_pos.
Axiom proof_of_mpn_copyd_partial_solve_wit_1 : mpn_copyd_partial_solve_wit_1.
Axiom proof_of_mpn_copyd_partial_solve_wit_2_off_zero_pure : mpn_copyd_partial_solve_wit_2_off_zero_pure.
Axiom proof_of_mpn_copyd_partial_solve_wit_2_off_zero : mpn_copyd_partial_solve_wit_2_off_zero.
Axiom proof_of_mpn_copyd_partial_solve_wit_3_off_pos_pure : mpn_copyd_partial_solve_wit_3_off_pos_pure.
Axiom proof_of_mpn_copyd_partial_solve_wit_3_off_pos : mpn_copyd_partial_solve_wit_3_off_pos.
Axiom proof_of_mpn_copyd_partial_solve_wit_4_off_zero : mpn_copyd_partial_solve_wit_4_off_zero.
Axiom proof_of_mpn_copyd_partial_solve_wit_5_off_zero : mpn_copyd_partial_solve_wit_5_off_zero.
Axiom proof_of_mpn_copyd_partial_solve_wit_6_off_pos : mpn_copyd_partial_solve_wit_6_off_pos.
Axiom proof_of_mpn_copyd_partial_solve_wit_7_off_pos : mpn_copyd_partial_solve_wit_7_off_pos.
Axiom proof_of_mpn_copyd_which_implies_wit_1 : mpn_copyd_which_implies_wit_1.
Axiom proof_of_mpn_copyd_which_implies_wit_2 : mpn_copyd_which_implies_wit_2.
Axiom proof_of_mpn_copyd_which_implies_wit_3 : mpn_copyd_which_implies_wit_3.
Axiom proof_of_mpn_zero_safety_wit_1 : mpn_zero_safety_wit_1.
Axiom proof_of_mpn_zero_safety_wit_2 : mpn_zero_safety_wit_2.
Axiom proof_of_mpn_zero_safety_wit_3 : mpn_zero_safety_wit_3.
Axiom proof_of_mpn_zero_safety_wit_4 : mpn_zero_safety_wit_4.
Axiom proof_of_mpn_zero_entail_wit_1 : mpn_zero_entail_wit_1.
Axiom proof_of_mpn_zero_entail_wit_2 : mpn_zero_entail_wit_2.
Axiom proof_of_mpn_zero_return_wit_1 : mpn_zero_return_wit_1.
Axiom proof_of_mpn_zero_partial_solve_wit_1 : mpn_zero_partial_solve_wit_1.
Axiom proof_of_mpn_zero_partial_solve_wit_2_pure : mpn_zero_partial_solve_wit_2_pure.
Axiom proof_of_mpn_zero_partial_solve_wit_2 : mpn_zero_partial_solve_wit_2.
Axiom proof_of_mpn_zero_partial_solve_wit_3 : mpn_zero_partial_solve_wit_3.
Axiom proof_of_mpn_zero_which_implies_wit_1 : mpn_zero_which_implies_wit_1.
Axiom proof_of_mpn_zero_which_implies_wit_2 : mpn_zero_which_implies_wit_2.
Axiom proof_of_mpn_lshift_safety_wit_1 : mpn_lshift_safety_wit_1.
Axiom proof_of_mpn_lshift_safety_wit_2_off_zero : mpn_lshift_safety_wit_2_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_3_off_pos : mpn_lshift_safety_wit_3_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_4_off_zero : mpn_lshift_safety_wit_4_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_5_off_zero : mpn_lshift_safety_wit_5_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_6_off_pos : mpn_lshift_safety_wit_6_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_7_off_pos : mpn_lshift_safety_wit_7_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_8_off_zero : mpn_lshift_safety_wit_8_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_9_off_pos : mpn_lshift_safety_wit_9_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_10_off_zero : mpn_lshift_safety_wit_10_off_zero.
Axiom proof_of_mpn_lshift_safety_wit_11_off_pos : mpn_lshift_safety_wit_11_off_pos.
Axiom proof_of_mpn_lshift_safety_wit_12_off_zero_inv : mpn_lshift_safety_wit_12_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_13_off_pos_inv : mpn_lshift_safety_wit_13_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_14_off_zero_inv : mpn_lshift_safety_wit_14_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_15_off_zero_inv : mpn_lshift_safety_wit_15_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_16_off_pos_inv : mpn_lshift_safety_wit_16_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_17_off_pos_inv : mpn_lshift_safety_wit_17_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_18_off_pos_inv : mpn_lshift_safety_wit_18_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_19_off_zero_inv : mpn_lshift_safety_wit_19_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_20_off_zero_inv : mpn_lshift_safety_wit_20_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_21_off_pos_inv : mpn_lshift_safety_wit_21_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_22_off_zero_inv : mpn_lshift_safety_wit_22_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_23_off_pos_inv : mpn_lshift_safety_wit_23_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_24_off_zero_inv : mpn_lshift_safety_wit_24_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_25_off_pos_inv : mpn_lshift_safety_wit_25_off_pos_inv.
Axiom proof_of_mpn_lshift_safety_wit_26_off_zero_inv : mpn_lshift_safety_wit_26_off_zero_inv.
Axiom proof_of_mpn_lshift_safety_wit_27_off_pos_inv : mpn_lshift_safety_wit_27_off_pos_inv.
Axiom proof_of_mpn_lshift_entail_wit_1_off_zero : mpn_lshift_entail_wit_1_off_zero.
Axiom proof_of_mpn_lshift_entail_wit_2_off_pos : mpn_lshift_entail_wit_2_off_pos.
Axiom proof_of_mpn_lshift_entail_wit_3_off_zero_inv : mpn_lshift_entail_wit_3_off_zero_inv.
Axiom proof_of_mpn_lshift_entail_wit_4_off_pos_inv : mpn_lshift_entail_wit_4_off_pos_inv.
Axiom proof_of_mpn_lshift_entail_wit_5_off_zero_inv : mpn_lshift_entail_wit_5_off_zero_inv.
Axiom proof_of_mpn_lshift_entail_wit_6_off_pos_inv : mpn_lshift_entail_wit_6_off_pos_inv.
Axiom proof_of_mpn_lshift_entail_wit_7_off_zero_inv : mpn_lshift_entail_wit_7_off_zero_inv.
Axiom proof_of_mpn_lshift_entail_wit_8_off_pos_inv : mpn_lshift_entail_wit_8_off_pos_inv.
Axiom proof_of_mpn_lshift_entail_wit_9_off_zero_inv : mpn_lshift_entail_wit_9_off_zero_inv.
Axiom proof_of_mpn_lshift_entail_wit_10_off_pos_inv : mpn_lshift_entail_wit_10_off_pos_inv.
Axiom proof_of_mpn_lshift_return_wit_1_off_zero_inv : mpn_lshift_return_wit_1_off_zero_inv.
Axiom proof_of_mpn_lshift_return_wit_2_off_pos_inv : mpn_lshift_return_wit_2_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_1 : mpn_lshift_partial_solve_wit_1.
Axiom proof_of_mpn_lshift_partial_solve_wit_2_off_zero : mpn_lshift_partial_solve_wit_2_off_zero.
Axiom proof_of_mpn_lshift_partial_solve_wit_3_off_pos : mpn_lshift_partial_solve_wit_3_off_pos.
Axiom proof_of_mpn_lshift_partial_solve_wit_4_off_zero_inv : mpn_lshift_partial_solve_wit_4_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_5_off_pos_inv : mpn_lshift_partial_solve_wit_5_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_6_off_zero_inv_pure : mpn_lshift_partial_solve_wit_6_off_zero_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_6_off_zero_inv : mpn_lshift_partial_solve_wit_6_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_7_off_pos_inv_pure : mpn_lshift_partial_solve_wit_7_off_pos_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_7_off_pos_inv : mpn_lshift_partial_solve_wit_7_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_8_off_zero_inv : mpn_lshift_partial_solve_wit_8_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_9_off_pos_inv : mpn_lshift_partial_solve_wit_9_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_10_off_zero_inv_pure : mpn_lshift_partial_solve_wit_10_off_zero_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_10_off_zero_inv : mpn_lshift_partial_solve_wit_10_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_11_off_pos_inv_pure : mpn_lshift_partial_solve_wit_11_off_pos_inv_pure.
Axiom proof_of_mpn_lshift_partial_solve_wit_11_off_pos_inv : mpn_lshift_partial_solve_wit_11_off_pos_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_12_off_zero_inv : mpn_lshift_partial_solve_wit_12_off_zero_inv.
Axiom proof_of_mpn_lshift_partial_solve_wit_13_off_pos_inv : mpn_lshift_partial_solve_wit_13_off_pos_inv.
Axiom proof_of_mpn_lshift_which_implies_wit_1 : mpn_lshift_which_implies_wit_1.
Axiom proof_of_mpn_lshift_which_implies_wit_2 : mpn_lshift_which_implies_wit_2.
Axiom proof_of_mpn_lshift_which_implies_wit_3 : mpn_lshift_which_implies_wit_3.
Axiom proof_of_mpn_lshift_which_implies_wit_4 : mpn_lshift_which_implies_wit_4.
Axiom proof_of_mpn_lshift_which_implies_wit_5 : mpn_lshift_which_implies_wit_5.
Axiom proof_of_mpz_mul_2exp_safety_wit_1 : mpz_mul_2exp_safety_wit_1.
Axiom proof_of_mpz_mul_2exp_safety_wit_2 : mpz_mul_2exp_safety_wit_2.
Axiom proof_of_mpz_mul_2exp_safety_wit_3 : mpz_mul_2exp_safety_wit_3.
Axiom proof_of_mpz_mul_2exp_safety_wit_4 : mpz_mul_2exp_safety_wit_4.
Axiom proof_of_mpz_mul_2exp_safety_wit_5 : mpz_mul_2exp_safety_wit_5.
Axiom proof_of_mpz_mul_2exp_safety_wit_6 : mpz_mul_2exp_safety_wit_6.
Axiom proof_of_mpz_mul_2exp_safety_wit_7 : mpz_mul_2exp_safety_wit_7.
Axiom proof_of_mpz_mul_2exp_safety_wit_8 : mpz_mul_2exp_safety_wit_8.
Axiom proof_of_mpz_mul_2exp_safety_wit_9 : mpz_mul_2exp_safety_wit_9.
Axiom proof_of_mpz_mul_2exp_safety_wit_10 : mpz_mul_2exp_safety_wit_10.
Axiom proof_of_mpz_mul_2exp_safety_wit_11 : mpz_mul_2exp_safety_wit_11.
Axiom proof_of_mpz_mul_2exp_safety_wit_12 : mpz_mul_2exp_safety_wit_12.
Axiom proof_of_mpz_mul_2exp_safety_wit_13 : mpz_mul_2exp_safety_wit_13.
Axiom proof_of_mpz_mul_2exp_safety_wit_14 : mpz_mul_2exp_safety_wit_14.
Axiom proof_of_mpz_mul_2exp_safety_wit_15 : mpz_mul_2exp_safety_wit_15.
Axiom proof_of_mpz_mul_2exp_safety_wit_16 : mpz_mul_2exp_safety_wit_16.
Axiom proof_of_mpz_mul_2exp_safety_wit_17 : mpz_mul_2exp_safety_wit_17.
Axiom proof_of_mpz_mul_2exp_safety_wit_18 : mpz_mul_2exp_safety_wit_18.
Axiom proof_of_mpz_mul_2exp_safety_wit_19 : mpz_mul_2exp_safety_wit_19.
Axiom proof_of_mpz_mul_2exp_safety_wit_20 : mpz_mul_2exp_safety_wit_20.
Axiom proof_of_mpz_mul_2exp_safety_wit_21 : mpz_mul_2exp_safety_wit_21.
Axiom proof_of_mpz_mul_2exp_safety_wit_22 : mpz_mul_2exp_safety_wit_22.
Axiom proof_of_mpz_mul_2exp_safety_wit_23 : mpz_mul_2exp_safety_wit_23.
Axiom proof_of_mpz_mul_2exp_safety_wit_24 : mpz_mul_2exp_safety_wit_24.
Axiom proof_of_mpz_mul_2exp_safety_wit_25 : mpz_mul_2exp_safety_wit_25.
Axiom proof_of_mpz_mul_2exp_entail_wit_1 : mpz_mul_2exp_entail_wit_1.
Axiom proof_of_mpz_mul_2exp_entail_wit_2 : mpz_mul_2exp_entail_wit_2.
Axiom proof_of_mpz_mul_2exp_entail_wit_3 : mpz_mul_2exp_entail_wit_3.
Axiom proof_of_mpz_mul_2exp_entail_wit_4 : mpz_mul_2exp_entail_wit_4.
Axiom proof_of_mpz_mul_2exp_entail_wit_5 : mpz_mul_2exp_entail_wit_5.
Axiom proof_of_mpz_mul_2exp_return_wit_1 : mpz_mul_2exp_return_wit_1.
Axiom proof_of_mpz_mul_2exp_return_wit_2 : mpz_mul_2exp_return_wit_2.
Axiom proof_of_mpz_mul_2exp_return_wit_3 : mpz_mul_2exp_return_wit_3.
Axiom proof_of_mpz_mul_2exp_return_wit_4 : mpz_mul_2exp_return_wit_4.
Axiom proof_of_mpz_mul_2exp_return_wit_5 : mpz_mul_2exp_return_wit_5.
Axiom proof_of_mpz_mul_2exp_return_wit_6 : mpz_mul_2exp_return_wit_6.
Axiom proof_of_mpz_mul_2exp_return_wit_7 : mpz_mul_2exp_return_wit_7.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_1_pure : mpz_mul_2exp_partial_solve_wit_1_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_1 : mpz_mul_2exp_partial_solve_wit_1.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_2 : mpz_mul_2exp_partial_solve_wit_2.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_3_pure : mpz_mul_2exp_partial_solve_wit_3_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_3 : mpz_mul_2exp_partial_solve_wit_3.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_4_pure : mpz_mul_2exp_partial_solve_wit_4_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_4 : mpz_mul_2exp_partial_solve_wit_4.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_5_pure : mpz_mul_2exp_partial_solve_wit_5_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_5 : mpz_mul_2exp_partial_solve_wit_5.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_6 : mpz_mul_2exp_partial_solve_wit_6.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_7_pure : mpz_mul_2exp_partial_solve_wit_7_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_7 : mpz_mul_2exp_partial_solve_wit_7.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_8_pure : mpz_mul_2exp_partial_solve_wit_8_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_8 : mpz_mul_2exp_partial_solve_wit_8.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_9_pure : mpz_mul_2exp_partial_solve_wit_9_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_9 : mpz_mul_2exp_partial_solve_wit_9.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_10_pure : mpz_mul_2exp_partial_solve_wit_10_pure.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_10 : mpz_mul_2exp_partial_solve_wit_10.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_11 : mpz_mul_2exp_partial_solve_wit_11.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_12 : mpz_mul_2exp_partial_solve_wit_12.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_13 : mpz_mul_2exp_partial_solve_wit_13.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_14 : mpz_mul_2exp_partial_solve_wit_14.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_15 : mpz_mul_2exp_partial_solve_wit_15.
Axiom proof_of_mpz_mul_2exp_partial_solve_wit_16 : mpz_mul_2exp_partial_solve_wit_16.

End VC_Correct.
