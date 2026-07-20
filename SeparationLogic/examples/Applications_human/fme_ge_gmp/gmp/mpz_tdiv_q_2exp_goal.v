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

(*----- Function mpn_copyi -----*)

Definition mpn_copyi_safety_wit_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  “ ((False \/ (True /\ (off_shifted = 0))) \/ (True /\ (off_shifted > 0))) ”
.

Definition mpn_copyi_safety_wit_2_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (off_shifted = 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyi_safety_wit_3_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (off_shifted > 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |->_)
  **  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_copyi_safety_wit_4_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> d_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_copyi_safety_wit_5_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre i (i + 1 ) (replace_Znth ((i - i )) ((Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0)) ((sublist (i) ((i + 1 )) (l_shifted)))) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition mpn_copyi_entail_wit_1_off_zero := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)) ,
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)) ,
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
).

Definition mpn_copyi_entail_wit_1_off_zero_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted = 0)) ,
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
.

Definition mpn_copyi_entail_wit_2_off_pos := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)) ,
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)) ,
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_entail_wit_2_off_pos_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (n_pre >= 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) (PreH7 : (off_shifted > 0)) ,
  (UIntArray.full d_pre (n_pre + off_shifted ) l_shifted )
|--
  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
.

Definition mpn_copyi_entail_wit_3_off_zero := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (off_shifted = 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
|--
  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (s_pre = d_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 0 (sublist (0) (0) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 n_pre (sublist (0) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (off_shifted = 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  TT && emp 
|--
  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ ((@nil Z) = (sublist (0) (0) (l_shifted))) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_3_off_zero_split_goal_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (off_shifted = 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  ((Zlength (l_shifted)) = n_pre)
.

Definition mpn_copyi_entail_wit_3_off_zero_split_goal_2 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (off_shifted = 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  ((@nil Z) = (sublist (0) (0) (l_shifted)))
.

Definition mpn_copyi_entail_wit_4_off_pos := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (off_shifted > 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre 0 0 (@nil Z) )
  **  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 0 (sublist (off_shifted) ((off_shifted + 0 )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (off_shifted > 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  TT && emp 
|--
  “ ((@nil Z) = (sublist (off_shifted) ((off_shifted + 0 )) (l_shifted))) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_4_off_pos_split_goal_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (PreH1 : (off_shifted > 0)) (PreH2 : (n_pre >= 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH6 : (list_within_bound UINT_MOD l_shifted )) ,
  ((@nil Z) = (sublist (off_shifted) ((off_shifted + 0 )) (l_shifted)))
.

Definition mpn_copyi_entail_wit_5_off_zero := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  ((( &( "s" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
|--
  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (s_pre = d_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg d_pre 0 (i + 1 ) (sublist (0) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  TT && emp 
|--
  “ ((sublist (0) ((i + 1 )) (l_shifted)) = (app ((sublist (0) (i) (l_shifted))) ((sublist (i) ((i + 1 )) (l_shifted))))) ”
  &&  emp
).

Definition mpn_copyi_entail_wit_5_off_zero_split_goal_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  ((sublist (0) ((i + 1 )) (l_shifted)) = (app ((sublist (0) (i) (l_shifted))) ((sublist (i) ((i + 1 )) (l_shifted)))))
.

Definition mpn_copyi_entail_wit_6_off_pos := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre i (i + 1 ) (replace_Znth ((i - i )) ((Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0)) ((sublist (i) ((i + 1 )) (l_shifted)))) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
|--
  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre 0 (i + 1 ) (sublist (off_shifted) ((off_shifted + (i + 1 ) )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ ((sublist (off_shifted) ((off_shifted + (i + 1 ) )) (l_shifted)) = (app ((sublist (off_shifted) ((off_shifted + i )) (l_shifted))) ((replace_Znth ((i - i )) ((Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0)) ((sublist (i) ((i + 1 )) (l_shifted))))))) ”
  &&  (UIntArray.seg d_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_entail_wit_6_off_pos_split_goal_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ ((sublist (off_shifted) ((off_shifted + (i + 1 ) )) (l_shifted)) = (app ((sublist (off_shifted) ((off_shifted + i )) (l_shifted))) ((replace_Znth ((i - i )) ((Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0)) ((sublist (i) ((i + 1 )) (l_shifted))))))) ”
.

Definition mpn_copyi_entail_wit_6_off_pos_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
.

Definition mpn_copyi_return_wit_1_off_zero := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
  **  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) )
  **  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  TT && emp 
|--
  “ ((sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) = (app ((sublist (0) (i) (l_shifted))) ((sublist (i) (n_pre) (l_shifted))))) ”
  &&  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_return_wit_1_off_zero_split_goal_1 := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  ((sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) = (app ((sublist (0) (i) (l_shifted))) ((sublist (i) (n_pre) (l_shifted)))))
.

Definition mpn_copyi_return_wit_1_off_zero_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  TT && emp 
|--
  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
.

Definition mpn_copyi_return_wit_2_off_pos := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) )
  **  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) )
  **  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_return_wit_2_off_pos_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre 0 n_pre (sublist (off_shifted) ((off_shifted + n_pre )) (l_shifted)) )
  **  (UIntArray.seg d_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_1_off_zero_pure := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
  **  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
|--
  “ (d_pre = d_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ”
.

Definition mpn_copyi_partial_solve_wit_1_off_zero_aux := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
  **  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
|--
  “ (d_pre = d_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (s_pre = d_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> d_pre)
  **  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_1_off_zero := mpn_copyi_partial_solve_wit_1_off_zero_pure -> mpn_copyi_partial_solve_wit_1_off_zero_aux.

Definition mpn_copyi_partial_solve_wit_2_off_pos_pure := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )) ,
  ((( &( "d" ) )) # Ptr  |-> d_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ”
.

Definition mpn_copyi_partial_solve_wit_2_off_pos_aux := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted > 0)) (PreH3 : (n_pre >= 0)) (PreH4 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH5 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted > 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_2_off_pos := mpn_copyi_partial_solve_wit_2_off_pos_pure -> mpn_copyi_partial_solve_wit_2_off_pos_aux.

Definition mpn_copyi_partial_solve_wit_3_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (d_pre = d_pre)) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted = 0)) (PreH4 : (n_pre >= 0)) (PreH5 : (s_pre = d_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((Zlength (l_shifted)) = n_pre)) (PreH9 : (list_within_bound UINT_MOD l_shifted )) (PreH10 : (off_shifted = 0)) (PreH11 : (n_pre >= 0)) (PreH12 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH13 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH14 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH15 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
|--
  “ (i < n_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (s_pre = d_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((d_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist (i) ((i + 1 )) (l_shifted)) 0))
  **  (UIntArray.missing_i d_pre i i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_4_off_zero := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (off_shifted = 0)) (PreH3 : (n_pre >= 0)) (PreH4 : (s_pre = d_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((Zlength (l_shifted)) = n_pre)) (PreH8 : (list_within_bound UINT_MOD l_shifted )) (PreH9 : (off_shifted = 0)) (PreH10 : (n_pre >= 0)) (PreH11 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH12 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH13 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH14 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
|--
  “ (i < n_pre) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ (s_pre = d_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted = 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((d_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i d_pre i i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (0) (i) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_5_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((s_pre + (i * sizeof(UINT)))) # UInt  |-> (Znth (i - i ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) 0))
  **  (UIntArray.missing_i s_pre i i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
.

Definition mpn_copyi_partial_solve_wit_6_off_pos := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (i < n_pre)) (PreH3 : (off_shifted > 0)) (PreH4 : (n_pre >= 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH10 : (list_within_bound UINT_MOD l_shifted )) (PreH11 : (off_shifted > 0)) (PreH12 : (n_pre >= 0)) (PreH13 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH14 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH15 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) (PreH16 : (list_within_bound UINT_MOD l_shifted )) ,
  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ” 
  &&  “ (off_shifted > 0) ” 
  &&  “ (n_pre >= 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_shifted ) ”
  &&  (((d_pre + (i * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i d_pre i i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
  **  (UIntArray.seg d_pre 0 i (sublist (off_shifted) ((off_shifted + i )) (l_shifted)) )
.

Definition mpn_copyi_which_implies_wit_1 := 
(
forall (n_pre: Z) (d_pre: Z) (l_shifted: (@list Z)) (s: Z) (i: Z) (PreH1 : (s = d_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_shifted)) = n_pre)) ,
  (UIntArray.seg d_pre i n_pre (sublist (i) (n_pre) (l_shifted)) )
|--
  “ (s = d_pre) ”
  &&  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) n_pre (sublist ((i + 1 )) (n_pre) (l_shifted)) )
) \/
(
forall (n_pre: Z) (d_pre: Z) (l_shifted: (@list Z)) (s: Z) (i: Z) (PreH1 : (s = d_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_shifted)) = n_pre)) ,
  TT && emp 
|--
  “ ((sublist (i) (n_pre) (l_shifted)) = (app ((sublist (i) ((i + 1 )) (l_shifted))) ((sublist ((i + 1 )) (n_pre) (l_shifted))))) ” 
  &&  “ ((Zlength ((sublist (i) ((i + 1 )) (l_shifted)))) = ((i + 1 ) - i )) ”
  &&  emp
).

Definition mpn_copyi_which_implies_wit_1_split_goal_1 := 
forall (n_pre: Z) (d_pre: Z) (l_shifted: (@list Z)) (s: Z) (i: Z) (PreH1 : (s = d_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_shifted)) = n_pre)) ,
  ((sublist (i) (n_pre) (l_shifted)) = (app ((sublist (i) ((i + 1 )) (l_shifted))) ((sublist ((i + 1 )) (n_pre) (l_shifted)))))
.

Definition mpn_copyi_which_implies_wit_1_split_goal_2 := 
forall (n_pre: Z) (d_pre: Z) (l_shifted: (@list Z)) (s: Z) (i: Z) (PreH1 : (s = d_pre)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : ((Zlength (l_shifted)) = n_pre)) ,
  ((Zlength ((sublist (i) ((i + 1 )) (l_shifted)))) = ((i + 1 ) - i ))
.

Definition mpn_copyi_which_implies_wit_2 := 
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) ,
  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  “ (s_pre = (d_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
) \/
(
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) ,
  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
).

Definition mpn_copyi_which_implies_wit_2_split_goal_spatial := 
forall (n_pre: Z) (s_pre: Z) (d_pre: Z) (off_shifted: Z) (l_shifted: (@list Z)) (i: Z) (PreH1 : (s_pre = (d_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (off_shifted > 0)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : ((Zlength (l_shifted)) = (n_pre + off_shifted ))) ,
  (UIntArray.seg d_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_shifted)) )
|--
  (UIntArray.seg d_pre i (i + 1 ) (sublist (i) ((i + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre (i + 1 ) (off_shifted + i ) (sublist ((i + 1 )) ((off_shifted + i )) (l_shifted)) )
  **  (UIntArray.seg s_pre i (i + 1 ) (sublist ((off_shifted + i )) (((off_shifted + i ) + 1 )) (l_shifted)) )
  **  (UIntArray.seg d_pre ((off_shifted + i ) + 1 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 1 )) ((n_pre + off_shifted )) (l_shifted)) )
.

(*----- Function mpn_rshift -----*)

Definition mpn_rshift_safety_wit_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) ,
  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpn_rshift_safety_wit_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_safety_wit_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> (up_pre + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
  **  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0))
|--
  “ ((32 - cnt_pre ) <= 31) ” 
  &&  “ (0 <= (32 - cnt_pre )) ”
.

Definition mpn_rshift_safety_wit_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> (up_pre + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
  **  ((( &( "retval" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0))
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_rshift_safety_wit_5 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> (up_pre + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
  **  ((( &( "retval" ) )) # UInt  |-> (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)))
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre))
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0))
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition mpn_rshift_safety_wit_6 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i: Z) (rp: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = ((n_pre - i ) - 1 ))) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : (0 <= i)) (PreH12 : (i < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : ((Zlength (l_done)) = i)) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done )) (PreH17 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH18 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH19 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH20 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> up)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_safety_wit_7 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> up)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_safety_wit_8 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> (up + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_safety_wit_9 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> (up + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (tnc <= 31) ” 
  &&  “ (0 <= tnc) ”
.

Definition mpn_rshift_safety_wit_10 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.full rp 1 (replace_Znth (0) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) tnc)) (32)))) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> (rp + (1 * sizeof(UINT))))
  **  ((( &( "up" ) )) # Ptr  |-> (up + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (cnt_pre <= 31) ” 
  &&  “ (0 <= cnt_pre) ”
.

Definition mpn_rshift_safety_wit_11 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.full rp 1 (replace_Znth (0) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) tnc)) (32)))) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  ((( &( "rp" ) )) # Ptr  |-> (rp + (1 * sizeof(UINT))))
  **  ((( &( "up" ) )) # Ptr  |-> (up + (1 * sizeof(UINT))))
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  ((( &( "low_limb" ) )) # UInt  |-> (Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre))
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - 1 )) ”
.

Definition mpn_rshift_safety_wit_12 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  ((( &( "rp" ) )) # Ptr  |-> rp)
  **  ((( &( "up" ) )) # Ptr  |-> up)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  ((( &( "tnc" ) )) # UInt  |-> tnc)
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  ((( &( "retval" ) )) # UInt  |-> retval)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpn_rshift_entail_wit_1 := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z))  (i: Z) ,
  “ ((up_pre + (1 * sizeof(UINT))) = (up_pre + ((i + 1 ) * sizeof(UINT)))) ” 
  &&  “ ((n_pre - 1 ) = ((n_pre - i ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ ((32 - cnt_pre ) = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (l_done = (@nil Z)) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ” 
  &&  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + 0 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) ((@nil Z))) + ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) (0)) ) ) * (Z.pow (2) (cnt_pre)) ) + ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ” 
  &&  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + 0 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) = (Znth ((off_shifted + 0 )) (l_up_shifted) (0))) ” 
  &&  “ (list_within_bound UINT_MOD (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (UIntArray.seg rp_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_1_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + 0 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) ((@nil Z))) + ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) (0)) ) ) * (Z.pow (2) (cnt_pre)) ) + ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) (32 - cnt_pre ))) (32)) = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + 0 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0) = (Znth ((off_shifted + 0 )) (l_up_shifted) (0))) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_5 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (list_within_bound UINT_MOD (@nil Z) ) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_6 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition mpn_rshift_entail_wit_1_split_goal_spatial := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  (UIntArray.seg rp_pre 0 (n_pre + off_shifted ) (sublist (0) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_entail_wit_2 := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i_2: Z) (l_done_2: (@list Z)) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH2 : (n = ((n_pre - i_2 ) - 1 ))) (PreH3 : (off_shifted >= 0)) (PreH4 : (n_pre > 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (tnc = (32 - cnt_pre ))) (PreH9 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (i_2 = 0)) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : (l_done_2 = (@nil Z))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z))  (i: Z) ,
  “ (rp_pre = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ” 
  &&  “ (n = ((n_pre - i ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i_2: Z) (l_done_2: (@list Z)) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH2 : (n = ((n_pre - i_2 ) - 1 ))) (PreH3 : (off_shifted >= 0)) (PreH4 : (n_pre > 0)) (PreH5 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH6 : (1 <= cnt_pre)) (PreH7 : (cnt_pre < 32)) (PreH8 : (tnc = (32 - cnt_pre ))) (PreH9 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH10 : (i_2 = 0)) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : (l_done_2 = (@nil Z))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) ,
  “ (rp_pre = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ” 
  &&  “ (n = ((n_pre - (Zlength (l_done)) ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= (Zlength (l_done))) ” 
  &&  “ ((Zlength (l_done)) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp_pre (Zlength (l_done)) (n_pre + off_shifted ) (sublist ((Zlength (l_done))) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_3 := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i_2: Z) (rp: Z) (PreH1 : (n <> 0)) (PreH2 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH3 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i_2 ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z))  (i: Z) ,
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (n = ((n_pre - i ) - 1 )) ” 
  &&  “ (n <> 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i_2: Z) (rp: Z) (PreH1 : (n <> 0)) (PreH2 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH3 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i_2 ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) ,
  “ (rp = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (n = ((n_pre - (Zlength (l_done)) ) - 1 )) ” 
  &&  “ (n <> 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (0 <= (Zlength (l_done))) ” 
  &&  “ (((Zlength (l_done)) + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp 0 1 (sublist ((Zlength (l_done))) (((Zlength (l_done)) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((Zlength (l_done)) + 1 ) ((off_shifted + (Zlength (l_done)) ) + 1 ) (sublist (((Zlength (l_done)) + 1 )) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + (Zlength (l_done)) ) + 1 )) (((off_shifted + (Zlength (l_done)) ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + (Zlength (l_done)) ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + (Zlength (l_done)) ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_4 := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.full rp 1 (replace_Znth (0) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) tnc)) (32)))) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z))  (i_2: Z) ,
  “ ((rp + (1 * sizeof(UINT))) = (rp_pre + (i_2 * sizeof(UINT)))) ” 
  &&  “ ((up + (1 * sizeof(UINT))) = (up_pre + ((i_2 + 1 ) * sizeof(UINT)))) ” 
  &&  “ ((n - 1 ) = ((n_pre - i_2 ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_done)) = i_2) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0))) ” 
  &&  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + ((Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i_2 l_done )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.full rp 1 (replace_Znth (0) ((Z.lor low_limb (unsigned_last_nbits ((Z.shiftl (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) tnc)) (32)))) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done_2 )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) ,
  “ ((rp + (1 * sizeof(UINT))) = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ” 
  &&  “ ((up + (1 * sizeof(UINT))) = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ” 
  &&  “ ((n - 1 ) = ((n_pre - (Zlength (l_done)) ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= (Zlength (l_done))) ” 
  &&  “ ((Zlength (l_done)) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ ((Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ” 
  &&  “ ((Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre) = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + ((Z.shiftr (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0) cnt_pre) * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp_pre (Zlength (l_done)) (n_pre + off_shifted ) (sublist ((Zlength (l_done))) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_5 := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i_2: Z) (l_done_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH3 : (n = ((n_pre - i_2 ) - 1 ))) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : ((Zlength (l_done_2)) = i_2)) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH18 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH19 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH20 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z))  (i: Z) ,
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ” 
  &&  “ (n = ((n_pre - i ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre i (n_pre + off_shifted ) (sublist (i) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i_2: Z) (l_done_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH3 : (n = ((n_pre - i_2 ) - 1 ))) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : (0 <= i_2)) (PreH12 : (i_2 < n_pre)) (PreH13 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH14 : ((Zlength (l_done_2)) = i_2)) (PreH15 : (list_within_bound UINT_MOD l_up_shifted )) (PreH16 : (list_within_bound UINT_MOD l_done_2 )) (PreH17 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH18 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH19 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH20 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) ,
  “ (rp = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ” 
  &&  “ (n = ((n_pre - (Zlength (l_done)) ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= (Zlength (l_done))) ” 
  &&  “ ((Zlength (l_done)) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp_pre (Zlength (l_done)) (n_pre + off_shifted ) (sublist ((Zlength (l_done))) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_6 := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i_2: Z) (rp: Z) (PreH1 : (n = 0)) (PreH2 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH3 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i_2 ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z))  (i: Z) ,
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ” 
  &&  “ (n = 0) ” 
  &&  “ (n = ((n_pre - i ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (retval: Z) (low_limb: Z) (high_limb: Z) (l_done_2: (@list Z)) (tnc: Z) (n: Z) (up: Z) (i_2: Z) (rp: Z) (PreH1 : (n = 0)) (PreH2 : (rp = (rp_pre + (i_2 * sizeof(UINT))))) (PreH3 : (up = (up_pre + ((i_2 + 1 ) * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i_2 ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i_2)) (PreH13 : (i_2 < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done_2)) = i_2)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done_2 )) (PreH18 : (high_limb = (Znth ((off_shifted + i_2 )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i_2 )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i_2 ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done_2)) + (low_limb * (Z.pow (UINT_MOD) (i_2)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i_2 l_done_2 )
  **  (UIntArray.seg rp_pre i_2 (n_pre + off_shifted ) (sublist (i_2) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_done: (@list Z)) ,
  “ (rp = (rp_pre + ((Zlength (l_done)) * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + (((Zlength (l_done)) + 1 ) * sizeof(UINT)))) ” 
  &&  “ (n = 0) ” 
  &&  “ (n = ((n_pre - (Zlength (l_done)) ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= (Zlength (l_done))) ” 
  &&  “ ((Zlength (l_done)) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + (Zlength (l_done)) )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + (Zlength (l_done)) ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) ((Zlength (l_done)))) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 (Zlength (l_done)) l_done )
  **  (UIntArray.seg rp 0 1 (sublist ((Zlength (l_done))) (((Zlength (l_done)) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((Zlength (l_done)) + 1 ) (n_pre + off_shifted ) (sublist (((Zlength (l_done)) + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_entail_wit_7 := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.full rp 1 (replace_Znth (0) (low_limb) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  ((( &( "high_limb" ) )) # UInt  |-> high_limb)
  **  ((( &( "low_limb" ) )) # UInt  |-> low_limb)
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_out: (@list Z)) ,
  “ (rp = (rp_pre + ((n_pre - 1 ) * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + (n_pre * sizeof(UINT)))) ” 
  &&  “ (n = 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  (UIntArray.seg rp_pre 0 n_pre l_out )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.full rp 1 (replace_Znth (0) (low_limb) ((sublist (i) ((i + 1 )) (l_up_shifted)))) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_out: (@list Z)) ,
  “ (rp = (rp_pre + ((n_pre - 1 ) * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + (n_pre * sizeof(UINT)))) ” 
  &&  “ (n = 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (UIntArray.seg rp_pre 0 n_pre l_out )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_return_wit_1 := 
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_out_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (retval: Z) (PreH1 : (rp = (rp_pre + ((n_pre - 1 ) * sizeof(UINT))))) (PreH2 : (up = (up_pre + (n_pre * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH12 : ((Zlength (l_out_2)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_out_2 )) (PreH15 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH16 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out_2)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 n_pre l_out_2 )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  EX (l_out: (@list Z)) ,
  “ ((Zlength (l_out)) = n_pre) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ”
  &&  (UIntArray.seg rp_pre 0 n_pre l_out )
  **  (UIntArray.seg rp_pre n_pre (n_pre + off_shifted ) (sublist (n_pre) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_out_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (retval: Z) (PreH1 : (rp = (rp_pre + ((n_pre - 1 ) * sizeof(UINT))))) (PreH2 : (up = (up_pre + (n_pre * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH12 : ((Zlength (l_out_2)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_out_2 )) (PreH15 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH16 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out_2)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  TT && emp 
|--
  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out_2)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32))) ”
  &&  emp
).

Definition mpn_rshift_return_wit_1_split_goal_1 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_out_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (retval: Z) (PreH1 : (rp = (rp_pre + ((n_pre - 1 ) * sizeof(UINT))))) (PreH2 : (up = (up_pre + (n_pre * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH12 : ((Zlength (l_out_2)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_out_2 )) (PreH15 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH16 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out_2)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out_2)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) ((32 - cnt_pre ))) ) ))
.

Definition mpn_rshift_return_wit_1_split_goal_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (l_out_2: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (retval: Z) (PreH1 : (rp = (rp_pre + ((n_pre - 1 ) * sizeof(UINT))))) (PreH2 : (up = (up_pre + (n_pre * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (off_shifted >= 0)) (PreH5 : (n_pre > 0)) (PreH6 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH7 : (1 <= cnt_pre)) (PreH8 : (cnt_pre < 32)) (PreH9 : (tnc = (32 - cnt_pre ))) (PreH10 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH11 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH12 : ((Zlength (l_out_2)) = n_pre)) (PreH13 : (list_within_bound UINT_MOD l_up_shifted )) (PreH14 : (list_within_bound UINT_MOD l_out_2 )) (PreH15 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH16 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) ((off_shifted + n_pre )) (l_up_shifted)))) = (((list_to_Z (UINT_MOD) (l_out_2)) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) ((32 - cnt_pre ))) )) (32)))
.

Definition mpn_rshift_partial_solve_wit_1_pure := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) ,
  ((( &( "retval" ) )) # UInt  |->_)
  **  ((( &( "tnc" ) )) # UInt  |-> (32 - cnt_pre ))
  **  ((( &( "low_limb" ) )) # UInt  |->_)
  **  ((( &( "high_limb" ) )) # UInt  |->_)
  **  ((( &( "rp" ) )) # Ptr  |-> rp_pre)
  **  ((( &( "up" ) )) # Ptr  |-> up_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "cnt" ) )) # UInt  |-> cnt_pre)
  **  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ”
.

Definition mpn_rshift_partial_solve_wit_1_aux := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH3 : (off_shifted >= 0)) (PreH4 : (1 <= cnt_pre)) (PreH5 : (cnt_pre < 32)) (PreH6 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH7 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH8 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
.

Definition mpn_rshift_partial_solve_wit_1 := mpn_rshift_partial_solve_wit_1_pure -> mpn_rshift_partial_solve_wit_1_aux.

Definition mpn_rshift_partial_solve_wit_2 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (off_shifted >= 0)) (PreH5 : (1 <= cnt_pre)) (PreH6 : (cnt_pre < 32)) (PreH7 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH8 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH9 : (list_within_bound UINT_MOD l_up_shifted )) ,
  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ”
  &&  (((up_pre + (0 * sizeof(UINT)))) # UInt  |-> (Znth (0 - 0 ) (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up_pre 0 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_partial_solve_wit_3 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (n = ((n_pre - i ) - 1 )) ” 
  &&  “ (n <> 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (((up + (0 * sizeof(UINT)))) # UInt  |-> (Znth (0 - 0 ) (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) 0))
  **  (UIntArray.missing_i up 0 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_partial_solve_wit_4 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (n <> 0)) (PreH6 : (off_shifted >= 0)) (PreH7 : (n_pre > 0)) (PreH8 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH9 : (1 <= cnt_pre)) (PreH10 : (cnt_pre < 32)) (PreH11 : (tnc = (32 - cnt_pre ))) (PreH12 : (0 <= i)) (PreH13 : ((i + 1 ) < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (n = ((n_pre - i ) - 1 )) ” 
  &&  “ (n <> 0) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (((rp + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp 0 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg up 0 1 (sublist (((off_shifted + i ) + 1 )) (((off_shifted + i ) + 2 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) ((off_shifted + i ) + 1 ) (sublist ((i + 1 )) (((off_shifted + i ) + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre ((off_shifted + i ) + 2 ) (n_pre + off_shifted ) (sublist (((off_shifted + i ) + 2 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_partial_solve_wit_5 := 
forall (cnt_pre: Z) (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (i: Z) (l_done: (@list Z)) (rp: Z) (up: Z) (n: Z) (tnc: Z) (high_limb: Z) (low_limb: Z) (retval: Z) (PreH1 : (rp = (rp_pre + (i * sizeof(UINT))))) (PreH2 : (up = (up_pre + ((i + 1 ) * sizeof(UINT))))) (PreH3 : (n = 0)) (PreH4 : (n = ((n_pre - i ) - 1 ))) (PreH5 : (off_shifted >= 0)) (PreH6 : (n_pre > 0)) (PreH7 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH8 : (1 <= cnt_pre)) (PreH9 : (cnt_pre < 32)) (PreH10 : (tnc = (32 - cnt_pre ))) (PreH11 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH12 : (0 <= i)) (PreH13 : (i < n_pre)) (PreH14 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) (PreH15 : ((Zlength (l_done)) = i)) (PreH16 : (list_within_bound UINT_MOD l_up_shifted )) (PreH17 : (list_within_bound UINT_MOD l_done )) (PreH18 : (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0)))) (PreH19 : (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) ))) (PreH20 : (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32)))) (PreH21 : ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) ))) ,
  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
|--
  “ (rp = (rp_pre + (i * sizeof(UINT)))) ” 
  &&  “ (up = (up_pre + ((i + 1 ) * sizeof(UINT)))) ” 
  &&  “ (n = 0) ” 
  &&  “ (n = ((n_pre - i ) - 1 )) ” 
  &&  “ (off_shifted >= 0) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((n_pre + off_shifted ) <= INT_MAX) ” 
  &&  “ (1 <= cnt_pre) ” 
  &&  “ (cnt_pre < 32) ” 
  &&  “ (tnc = (32 - cnt_pre )) ” 
  &&  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((Zlength (l_up_shifted)) = (n_pre + off_shifted )) ” 
  &&  “ ((Zlength (l_done)) = i) ” 
  &&  “ (list_within_bound UINT_MOD l_up_shifted ) ” 
  &&  “ (list_within_bound UINT_MOD l_done ) ” 
  &&  “ (high_limb = (Znth ((off_shifted + i )) (l_up_shifted) (0))) ” 
  &&  “ (low_limb = ((Znth ((off_shifted + i )) (l_up_shifted) (0)) ÷ (Z.pow (2) (cnt_pre)) )) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (off_shifted) (l_up_shifted) (0)) * (Z.pow (2) (tnc)) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (off_shifted) (((off_shifted + i ) + 1 )) (l_up_shifted)))) = ((((list_to_Z (UINT_MOD) (l_done)) + (low_limb * (Z.pow (UINT_MOD) (i)) ) ) * (Z.pow (2) (cnt_pre)) ) + (retval ÷ (Z.pow (2) (tnc)) ) )) ”
  &&  (((rp + (0 * sizeof(UINT)))) # UInt  |->_)
  **  (UIntArray.missing_i rp 0 0 1 (sublist (i) ((i + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre 0 i l_done )
  **  (UIntArray.seg rp_pre (i + 1 ) (n_pre + off_shifted ) (sublist ((i + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

Definition mpn_rshift_which_implies_wit_1 := 
(
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (off_shifted >= 0)) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) ,
  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  “ (up_pre = (rp_pre + (off_shifted * sizeof(UINT)))) ”
  &&  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
) \/
(
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (off_shifted >= 0)) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) ,
  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
).

Definition mpn_rshift_which_implies_wit_1_split_goal_spatial := 
forall (n_pre: Z) (up_pre: Z) (rp_pre: Z) (off_shifted: Z) (l_up_shifted: (@list Z)) (PreH1 : (off_shifted >= 0)) (PreH2 : (n_pre > 0)) (PreH3 : ((n_pre + off_shifted ) <= INT_MAX)) (PreH4 : (up_pre = (rp_pre + (off_shifted * sizeof(UINT))))) (PreH5 : ((Zlength (l_up_shifted)) = (n_pre + off_shifted ))) ,
  (UIntArray.full rp_pre (n_pre + off_shifted ) l_up_shifted )
|--
  (UIntArray.seg rp_pre 0 off_shifted (sublist (0) (off_shifted) (l_up_shifted)) )
  **  (UIntArray.seg up_pre 0 1 (sublist (off_shifted) ((off_shifted + 1 )) (l_up_shifted)) )
  **  (UIntArray.seg rp_pre (off_shifted + 1 ) (n_pre + off_shifted ) (sublist ((off_shifted + 1 )) ((n_pre + off_shifted )) (l_up_shifted)) )
.

(*----- Function mpz_div_q_2exp -----*)

Definition mpz_div_q_2exp_safety_wit_1 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (mode_pre = 2)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH5 : ((Zabs (size)) <= cap)) (PreH6 : (cap >= 0)) (PreH7 : (cap <= INT_MAX)) (PreH8 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_2 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_3 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <> 0) ”
.

Definition mpz_div_q_2exp_safety_wit_4 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_div_q_2exp_safety_wit_5 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
).

Definition mpz_div_q_2exp_safety_wit_5_split_goal_1 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
.

Definition mpz_div_q_2exp_safety_wit_5_split_goal_2 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((INT_MIN) <= (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ”
.

Definition mpz_div_q_2exp_safety_wit_6 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <> 0) ”
.

Definition mpz_div_q_2exp_safety_wit_7 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition mpz_div_q_2exp_safety_wit_8 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (retval = (Zabs (size)))) (PreH2 : (size <> 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_9 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size > 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size <> 0)) (PreH4 : (q_pre = u_pre)) (PreH5 : (mode_pre = 2)) (PreH6 : (bit_index_pre >= 0)) (PreH7 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (cap >= 0)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_div_q_2exp_safety_wit_10 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size <= 0)) (PreH2 : (retval = (Zabs (size)))) (PreH3 : (size <> 0)) (PreH4 : (q_pre = u_pre)) (PreH5 : (mode_pre = 2)) (PreH6 : (bit_index_pre >= 0)) (PreH7 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH8 : ((Zabs (size)) <= cap)) (PreH9 : (cap >= 0)) (PreH10 : (cap <= INT_MAX)) (PreH11 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_11 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre = 1)) (PreH2 : (size > 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_12 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre = 0)) (PreH2 : (size <= 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_13 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre <> 1)) (PreH2 : (size > 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_14 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre <> 0)) (PreH2 : (size <= 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_15 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre <> 1)) (PreH2 : (size > 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_16 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (mode_pre <> 0)) (PreH2 : (size <= 0)) (PreH3 : (retval = (Zabs (size)))) (PreH4 : (size <> 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : ((Zabs (size)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_17 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_18 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_19 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (mode_pre = 2)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH5 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH6 : (bit_index >= 0)) (PreH7 : (bit_index < 32)) (PreH8 : (un <> 0)) (PreH9 : ((Zabs (un)) <= cap)) (PreH10 : (cap >= 0)) (PreH11 : (cap <= INT_MAX)) (PreH12 : (same_sign z_eq_trunc un )) (PreH13 : (adjust = 0)) (PreH14 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH15 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH16 : (qn > 0)) (PreH17 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH18 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH19 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH20 : (list_within_bound UINT_MOD l )) (PreH21 : ((last (l) (1)) >= 1)) (PreH22 : (u__mp_size = un)) (PreH23 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH24 : (u__mp_d = qp)) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_20 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((qn - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (qn - 1 )) ”
.

Definition mpz_div_q_2exp_safety_wit_21 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((qn - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (qn - 0 )) ”
.

Definition mpz_div_q_2exp_safety_wit_22 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = qn)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH5 : (bit_index <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH11 : (bit_index >= 0)) (PreH12 : (bit_index < 32)) (PreH13 : (un <> 0)) (PreH14 : ((Zabs (un)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc un )) (PreH18 : (adjust = 0)) (PreH19 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH20 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH21 : (qn > 0)) (PreH22 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH23 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH24 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH25 : (list_within_bound UINT_MOD l )) (PreH26 : ((last (l) (1)) >= 1)) (PreH27 : (u__mp_size = un)) (PreH28 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH29 : (u__mp_d = qp)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((qn - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (qn - 1 )) ”
.

Definition mpz_div_q_2exp_safety_wit_23 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = qn)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH5 : (bit_index <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH11 : (bit_index >= 0)) (PreH12 : (bit_index < 32)) (PreH13 : (un <> 0)) (PreH14 : ((Zabs (un)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc un )) (PreH18 : (adjust = 0)) (PreH19 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH20 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH21 : (qn > 0)) (PreH22 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH23 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH24 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH25 : (list_within_bound UINT_MOD l )) (PreH26 : ((last (l) (1)) >= 1)) (PreH27 : (u__mp_size = un)) (PreH28 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH29 : (u__mp_d = qp)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition mpz_div_q_2exp_safety_wit_24 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = qn)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH5 : (bit_index <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH11 : (bit_index >= 0)) (PreH12 : (bit_index < 32)) (PreH13 : (un <> 0)) (PreH14 : ((Zabs (un)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc un )) (PreH18 : (adjust = 0)) (PreH19 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH20 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH21 : (qn > 0)) (PreH22 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH23 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH24 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH25 : (list_within_bound UINT_MOD l )) (PreH26 : ((last (l) (1)) >= 1)) (PreH27 : (u__mp_size = un)) (PreH28 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH29 : (u__mp_d = qp)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_25 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) (PreH31 : (adjust <> 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 0 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_26 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) (PreH31 : (adjust <> 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 1 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_27 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)) (PreH26 : (adjust <> 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> qn)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_28 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_29 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_30 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) (PreH31 : (adjust = 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 0 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_31 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) (PreH31 : (adjust = 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 1 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_32 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)) (PreH26 : (adjust = 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> qn)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition mpz_div_q_2exp_safety_wit_33 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH3 : (mode_pre <> 1)) (PreH4 : (size > 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (size <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc size )) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ False ”
.

Definition mpz_div_q_2exp_safety_wit_34 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size >= 0)) (PreH2 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH3 : (mode_pre <> 0)) (PreH4 : (size <= 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (size <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc size )) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ False ”
.

Definition mpz_div_q_2exp_entail_wit_1 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (mode_pre = 2)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) ,
  (store_Z q_pre z_eq_trunc )
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (mode_pre = 2)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) ,
  (store_Z q_pre z_eq_trunc )
|--
  EX (ptr: Z)  (cap: Z)  (size: Z) ,
  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
).

Definition mpz_div_q_2exp_entail_wit_2_1 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (size: Z) (cap_2: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : (same_sign z_eq_trunc size )) (PreH2 : (z_callee__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)))) (PreH3 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH4 : (mode_pre <> 1)) (PreH5 : (size > 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (size <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (cap_2 >= 0)) (PreH14 : (cap_2 <= INT_MAX)) (PreH15 : (same_sign z_eq_trunc size )) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (u__mp_d: Z)  (u__mp_alloc: Z)  (u__mp_size: Z)  (l: (@list Z))  (cap: Z) ,
  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) = (bit_index_pre % ( 32 ) )) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) >= 0) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) < 32) ” 
  &&  “ (size <> 0) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) = (bit_index_pre ÷ 32 )) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = ((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ” 
  &&  “ (((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = (Zabs (size))) ” 
  &&  “ ((Zlength (l)) = ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_size = size) ” 
  &&  “ (u__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap))) ” 
  &&  “ (u__mp_d = retval_2) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) l )
  **  (UIntArray.undef_seg retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)) )
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (size: Z) (cap_2: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : (z_callee__mp_alloc <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (z_callee__mp_alloc >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign z_eq_trunc size )) (PreH6 : (z_callee__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)))) (PreH7 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH8 : (mode_pre <> 1)) (PreH9 : (size > 0)) (PreH10 : (retval = (Zabs (size)))) (PreH11 : (size <> 0)) (PreH12 : (q_pre = u_pre)) (PreH13 : (mode_pre = 2)) (PreH14 : (bit_index_pre >= 0)) (PreH15 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH16 : ((Zabs (size)) <= cap_2)) (PreH17 : (cap_2 >= 0)) (PreH18 : (cap_2 <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc size )) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (l: (@list Z))  (cap: Z) ,
  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) >= 0) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) < 32) ” 
  &&  “ (size <> 0) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ” 
  &&  “ ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) = (bit_index_pre ÷ 32 )) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = ((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ” 
  &&  “ (((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = (Zabs (size))) ” 
  &&  “ ((Zlength (l)) = ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.full retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) l )
  **  (UIntArray.undef_seg retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)) )
).

Definition mpz_div_q_2exp_entail_wit_2_2 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (size: Z) (cap_2: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : (same_sign z_eq_trunc size )) (PreH2 : (z_callee__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)))) (PreH3 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH4 : (mode_pre <> 0)) (PreH5 : (size <= 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (size <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : ((Zabs (size)) <= cap_2)) (PreH13 : (cap_2 >= 0)) (PreH14 : (cap_2 <= INT_MAX)) (PreH15 : (same_sign z_eq_trunc size )) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (u__mp_d: Z)  (u__mp_alloc: Z)  (u__mp_size: Z)  (l: (@list Z))  (cap: Z) ,
  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) = (bit_index_pre % ( 32 ) )) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) >= 0) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) < 32) ” 
  &&  “ (size <> 0) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) = (bit_index_pre ÷ 32 )) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = ((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ” 
  &&  “ (((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = (Zabs (size))) ” 
  &&  “ ((Zlength (l)) = ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_size = size) ” 
  &&  “ (u__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap))) ” 
  &&  “ (u__mp_d = retval_2) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) l )
  **  (UIntArray.undef_seg retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)) )
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (size: Z) (cap_2: Z) (retval: Z) (z_callee__mp_alloc: Z) (retval_2: Z) (PreH1 : (z_callee__mp_alloc <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (z_callee__mp_alloc >= INT_MIN)) (PreH4 : (size >= INT_MIN)) (PreH5 : (same_sign z_eq_trunc size )) (PreH6 : (z_callee__mp_alloc = (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)))) (PreH7 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH8 : (mode_pre <> 0)) (PreH9 : (size <= 0)) (PreH10 : (retval = (Zabs (size)))) (PreH11 : (size <> 0)) (PreH12 : (q_pre = u_pre)) (PreH13 : (mode_pre = 2)) (PreH14 : (bit_index_pre >= 0)) (PreH15 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH16 : ((Zabs (size)) <= cap_2)) (PreH17 : (cap_2 >= 0)) (PreH18 : (cap_2 <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc size )) ,
  (mpd_store_Z_compact UINT_MOD retval_2 (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg retval_2 (Zabs (size)) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap_2)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> z_callee__mp_alloc)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
|--
  EX (l: (@list Z))  (cap: Z) ,
  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) >= 0) ” 
  &&  “ ((bit_index_pre % ( 32 ) ) < 32) ” 
  &&  “ (size <> 0) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ” 
  &&  “ ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) = (bit_index_pre ÷ 32 )) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = ((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ” 
  &&  “ (((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) = (Zabs (size))) ” 
  &&  “ ((Zlength (l)) = ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> retval_2)
  **  (UIntArray.full retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) l )
  **  (UIntArray.undef_seg retval_2 ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) + (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) (Z.max ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) )) (cap)) )
).

Definition mpz_div_q_2exp_entail_wit_3_1 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size < 0)) (PreH2 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH3 : (mode_pre <> 0)) (PreH4 : (size <= 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (size <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc size )) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "qn" ) )) # Int  |-> 0)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (q_pre = u_pre) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ (size < 0) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (cap >= INT_MIN)) (PreH2 : (size < 0)) (PreH3 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH4 : (mode_pre <> 0)) (PreH5 : (size <= 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (size <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : ((Zabs (size)) <= cap)) (PreH13 : (cap >= 0)) (PreH14 : (cap <= INT_MAX)) (PreH15 : (same_sign z_eq_trunc size )) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  EX (cap_2: Z)  (ptr_2: Z) ,
  “ (same_sign (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) 0 ) ” 
  &&  “ ((Zabs (0)) <= cap_2) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ (size < 0) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs (0)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))))) (Zabs (0)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_entail_wit_3_2 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (un < 0)) (PreH2 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH3 : ((Zlength (l_out)) = qn)) (PreH4 : (list_within_bound UINT_MOD l_out )) (PreH5 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH7 : (bit_index <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH13 : (bit_index >= 0)) (PreH14 : (bit_index < 32)) (PreH15 : (un <> 0)) (PreH16 : ((Zabs (un)) <= cap)) (PreH17 : (cap >= 0)) (PreH18 : (cap <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc un )) (PreH20 : (adjust = 0)) (PreH21 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH22 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH23 : (qn > 0)) (PreH24 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH25 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH26 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH27 : (list_within_bound UINT_MOD l )) (PreH28 : ((last (l) (1)) >= 1)) (PreH29 : (u__mp_size = un)) (PreH30 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH31 : (u__mp_d = qp)) (PreH32 : (adjust = 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 0 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 0 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ (un < 0) ” 
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un < 0)) (PreH4 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH5 : ((Zlength (l_out)) = qn)) (PreH6 : (list_within_bound UINT_MOD l_out )) (PreH7 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH9 : (bit_index <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH15 : (bit_index >= 0)) (PreH16 : (bit_index < 32)) (PreH17 : (un <> 0)) (PreH18 : ((Zabs (un)) <= cap)) (PreH19 : (cap >= 0)) (PreH20 : (cap <= INT_MAX)) (PreH21 : (same_sign z_eq_trunc un )) (PreH22 : (adjust = 0)) (PreH23 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH24 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH25 : (qn > 0)) (PreH26 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH27 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH28 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH29 : (list_within_bound UINT_MOD l )) (PreH30 : ((last (l) (1)) >= 1)) (PreH31 : (u__mp_size = un)) (PreH32 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH33 : (u__mp_d = qp)) (PreH34 : (adjust = 0)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) (qn - 0 ) ) ” 
  &&  “ ((Zabs ((qn - 0 ))) <= cap_2) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ (un < 0) ” 
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((qn - 0 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))))) (Zabs ((qn - 0 ))) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_entail_wit_3_3 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (un < 0)) (PreH2 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH3 : ((Zlength (l_out)) = qn)) (PreH4 : (list_within_bound UINT_MOD l_out )) (PreH5 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH7 : (bit_index <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH13 : (bit_index >= 0)) (PreH14 : (bit_index < 32)) (PreH15 : (un <> 0)) (PreH16 : ((Zabs (un)) <= cap)) (PreH17 : (cap >= 0)) (PreH18 : (cap <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc un )) (PreH20 : (adjust = 0)) (PreH21 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH22 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH23 : (qn > 0)) (PreH24 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH25 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH26 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH27 : (list_within_bound UINT_MOD l )) (PreH28 : ((last (l) (1)) >= 1)) (PreH29 : (u__mp_size = un)) (PreH30 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH31 : (u__mp_d = qp)) (PreH32 : (adjust = 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 1 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> (qn - 1 ))
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ (un < 0) ” 
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un < 0)) (PreH4 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH5 : ((Zlength (l_out)) = qn)) (PreH6 : (list_within_bound UINT_MOD l_out )) (PreH7 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH9 : (bit_index <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH15 : (bit_index >= 0)) (PreH16 : (bit_index < 32)) (PreH17 : (un <> 0)) (PreH18 : ((Zabs (un)) <= cap)) (PreH19 : (cap >= 0)) (PreH20 : (cap <= INT_MAX)) (PreH21 : (same_sign z_eq_trunc un )) (PreH22 : (adjust = 0)) (PreH23 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH24 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH25 : (qn > 0)) (PreH26 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH27 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH28 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH29 : (list_within_bound UINT_MOD l )) (PreH30 : ((last (l) (1)) >= 1)) (PreH31 : (u__mp_size = un)) (PreH32 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH33 : (u__mp_d = qp)) (PreH34 : (adjust = 0)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) (qn - 1 ) ) ” 
  &&  “ ((Zabs ((qn - 1 ))) <= cap_2) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ (un < 0) ” 
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((qn - 1 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))))) (Zabs ((qn - 1 ))) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_entail_wit_3_4 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (un < 0)) (PreH2 : (bit_index = 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH8 : (bit_index >= 0)) (PreH9 : (bit_index < 32)) (PreH10 : (un <> 0)) (PreH11 : ((Zabs (un)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc un )) (PreH15 : (adjust = 0)) (PreH16 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH17 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH18 : (qn > 0)) (PreH19 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH20 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH22 : (list_within_bound UINT_MOD l )) (PreH23 : ((last (l) (1)) >= 1)) (PreH24 : (u__mp_size = un)) (PreH25 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH26 : (u__mp_d = qp)) (PreH27 : (adjust = 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> qn)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ (un < 0) ” 
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un < 0)) (PreH4 : (bit_index = 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH10 : (bit_index >= 0)) (PreH11 : (bit_index < 32)) (PreH12 : (un <> 0)) (PreH13 : ((Zabs (un)) <= cap)) (PreH14 : (cap >= 0)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (same_sign z_eq_trunc un )) (PreH17 : (adjust = 0)) (PreH18 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH19 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH20 : (qn > 0)) (PreH21 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH22 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH23 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH24 : (list_within_bound UINT_MOD l )) (PreH25 : ((last (l) (1)) >= 1)) (PreH26 : (u__mp_size = un)) (PreH27 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH28 : (u__mp_d = qp)) (PreH29 : (adjust = 0)) ,
  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) qn ) ” 
  &&  “ ((Zabs (qn)) <= cap_2) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ (un < 0) ” 
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (UIntArray.undef_seg ptr (Zabs (qn)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))))) (Zabs (qn)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_1 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (cap >= INT_MIN)) (PreH2 : (size = 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : ((Zabs (size)) <= cap)) (PreH8 : (cap >= 0)) (PreH9 : (cap <= INT_MAX)) (PreH10 : (same_sign z_eq_trunc size )) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  EX (cap_2: Z)  (ptr_2: Z) ,
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) 0 ) ” 
  &&  “ ((Zabs (0)) <= cap_2) ” 
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs (0)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs (0)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_2 := 
(
forall (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (un: Z) (PreH1 : (q_pre = q_pre)) (PreH2 : (q_pre = u_pre)) (PreH3 : (bit_index_pre >= 0)) (PreH4 : (un < 0)) (PreH5 : (same_sign z_eq_trunc un )) ,
  (store_Z q_pre (-(Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre))))) )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (un: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (bit_index_pre >= 0)) (PreH3 : (un < 0)) (PreH4 : (same_sign z_eq_trunc un )) ,
  (store_Z q_pre (-(Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre))))) )
|--
  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
).

Definition mpz_div_q_2exp_return_wit_2_split_goal_spatial := 
forall (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (un: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (bit_index_pre >= 0)) (PreH3 : (un < 0)) (PreH4 : (same_sign z_eq_trunc un )) ,
  (store_Z q_pre (-(Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre))))) )
|--
  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
.

Definition mpz_div_q_2exp_return_wit_3 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (size >= 0)) (PreH2 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH3 : (mode_pre <> 1)) (PreH4 : (size > 0)) (PreH5 : (retval = (Zabs (size)))) (PreH6 : (size <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : ((Zabs (size)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc size )) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : (cap >= INT_MIN)) (PreH2 : (size >= 0)) (PreH3 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH4 : (mode_pre <> 1)) (PreH5 : (size > 0)) (PreH6 : (retval = (Zabs (size)))) (PreH7 : (size <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : ((Zabs (size)) <= cap)) (PreH13 : (cap >= 0)) (PreH14 : (cap <= INT_MAX)) (PreH15 : (same_sign z_eq_trunc size )) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  EX (cap_2: Z)  (ptr_2: Z) ,
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) 0 ) ” 
  &&  “ ((Zabs (0)) <= cap_2) ” 
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr_2 (Zabs (0)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr_2 (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs (0)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr_2)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_4 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (un >= 0)) (PreH2 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH3 : ((Zlength (l_out)) = qn)) (PreH4 : (list_within_bound UINT_MOD l_out )) (PreH5 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH7 : (bit_index <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH13 : (bit_index >= 0)) (PreH14 : (bit_index < 32)) (PreH15 : (un <> 0)) (PreH16 : ((Zabs (un)) <= cap)) (PreH17 : (cap >= 0)) (PreH18 : (cap <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc un )) (PreH20 : (adjust = 0)) (PreH21 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH22 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH23 : (qn > 0)) (PreH24 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH25 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH26 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH27 : (list_within_bound UINT_MOD l )) (PreH28 : ((last (l) (1)) >= 1)) (PreH29 : (u__mp_size = un)) (PreH30 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH31 : (u__mp_d = qp)) (PreH32 : (adjust = 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 0 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un >= 0)) (PreH4 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH5 : ((Zlength (l_out)) = qn)) (PreH6 : (list_within_bound UINT_MOD l_out )) (PreH7 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH9 : (bit_index <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH15 : (bit_index >= 0)) (PreH16 : (bit_index < 32)) (PreH17 : (un <> 0)) (PreH18 : ((Zabs (un)) <= cap)) (PreH19 : (cap >= 0)) (PreH20 : (cap <= INT_MAX)) (PreH21 : (same_sign z_eq_trunc un )) (PreH22 : (adjust = 0)) (PreH23 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH24 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH25 : (qn > 0)) (PreH26 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH27 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH28 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH29 : (list_within_bound UINT_MOD l )) (PreH30 : ((last (l) (1)) >= 1)) (PreH31 : (u__mp_size = un)) (PreH32 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH33 : (u__mp_d = qp)) (PreH34 : (adjust = 0)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) (qn - 0 ) ) ” 
  &&  “ ((Zabs ((qn - 0 ))) <= cap_2) ” 
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((qn - 0 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs ((qn - 0 ))) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_5 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (un >= 0)) (PreH2 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH3 : ((Zlength (l_out)) = qn)) (PreH4 : (list_within_bound UINT_MOD l_out )) (PreH5 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH6 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH7 : (bit_index <> 0)) (PreH8 : (q_pre = u_pre)) (PreH9 : (mode_pre = 2)) (PreH10 : (bit_index_pre >= 0)) (PreH11 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH12 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH13 : (bit_index >= 0)) (PreH14 : (bit_index < 32)) (PreH15 : (un <> 0)) (PreH16 : ((Zabs (un)) <= cap)) (PreH17 : (cap >= 0)) (PreH18 : (cap <= INT_MAX)) (PreH19 : (same_sign z_eq_trunc un )) (PreH20 : (adjust = 0)) (PreH21 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH22 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH23 : (qn > 0)) (PreH24 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH25 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH26 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH27 : (list_within_bound UINT_MOD l )) (PreH28 : ((last (l) (1)) >= 1)) (PreH29 : (u__mp_size = un)) (PreH30 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH31 : (u__mp_d = qp)) (PreH32 : (adjust = 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> (qn - 1 ))
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un >= 0)) (PreH4 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH5 : ((Zlength (l_out)) = qn)) (PreH6 : (list_within_bound UINT_MOD l_out )) (PreH7 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH8 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH9 : (bit_index <> 0)) (PreH10 : (q_pre = u_pre)) (PreH11 : (mode_pre = 2)) (PreH12 : (bit_index_pre >= 0)) (PreH13 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH14 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH15 : (bit_index >= 0)) (PreH16 : (bit_index < 32)) (PreH17 : (un <> 0)) (PreH18 : ((Zabs (un)) <= cap)) (PreH19 : (cap >= 0)) (PreH20 : (cap <= INT_MAX)) (PreH21 : (same_sign z_eq_trunc un )) (PreH22 : (adjust = 0)) (PreH23 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH24 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH25 : (qn > 0)) (PreH26 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH27 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH28 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH29 : (list_within_bound UINT_MOD l )) (PreH30 : ((last (l) (1)) >= 1)) (PreH31 : (u__mp_size = un)) (PreH32 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH33 : (u__mp_d = qp)) (PreH34 : (adjust = 0)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) (qn - 1 ) ) ” 
  &&  “ ((Zabs ((qn - 1 ))) <= cap_2) ” 
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs ((qn - 1 ))) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs ((qn - 1 ))) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_return_wit_6 := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (un >= 0)) (PreH2 : (bit_index = 0)) (PreH3 : (q_pre = u_pre)) (PreH4 : (mode_pre = 2)) (PreH5 : (bit_index_pre >= 0)) (PreH6 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH7 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH8 : (bit_index >= 0)) (PreH9 : (bit_index < 32)) (PreH10 : (un <> 0)) (PreH11 : ((Zabs (un)) <= cap)) (PreH12 : (cap >= 0)) (PreH13 : (cap <= INT_MAX)) (PreH14 : (same_sign z_eq_trunc un )) (PreH15 : (adjust = 0)) (PreH16 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH17 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH18 : (qn > 0)) (PreH19 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH20 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH21 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH22 : (list_within_bound UINT_MOD l )) (PreH23 : ((last (l) (1)) >= 1)) (PreH24 : (u__mp_size = un)) (PreH25 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH26 : (u__mp_d = qp)) (PreH27 : (adjust = 0)) ,
  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> qn)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (q_pre = u_pre) ”
  &&  (store_Z q_pre (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) )
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_alloc >= INT_MIN)) (PreH3 : (un >= 0)) (PreH4 : (bit_index = 0)) (PreH5 : (q_pre = u_pre)) (PreH6 : (mode_pre = 2)) (PreH7 : (bit_index_pre >= 0)) (PreH8 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH9 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH10 : (bit_index >= 0)) (PreH11 : (bit_index < 32)) (PreH12 : (un <> 0)) (PreH13 : ((Zabs (un)) <= cap)) (PreH14 : (cap >= 0)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (same_sign z_eq_trunc un )) (PreH17 : (adjust = 0)) (PreH18 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH19 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH20 : (qn > 0)) (PreH21 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH22 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH23 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH24 : (list_within_bound UINT_MOD l )) (PreH25 : ((last (l) (1)) >= 1)) (PreH26 : (u__mp_size = un)) (PreH27 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH28 : (u__mp_d = qp)) (PreH29 : (adjust = 0)) ,
  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  EX (cap_2: Z)  (ptr: Z) ,
  “ (same_sign (Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))) qn ) ” 
  &&  “ ((Zabs (qn)) <= cap_2) ” 
  &&  “ (q_pre = u_pre) ”
  &&  (UIntArray.undef_seg ptr (Zabs (qn)) cap_2 )
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs ((Z.quot (z_eq_trunc) ((Z.pow (2) (bit_index_pre)))))) (Zabs (qn)) )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap_2)
).

Definition mpz_div_q_2exp_partial_solve_wit_1 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size = 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_div_q_2exp_partial_solve_wit_2_pure := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ”
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (mode_pre <= INT_MAX)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH6 : (size >= INT_MIN)) (PreH7 : (mode_pre >= INT_MIN)) (PreH8 : (size <> 0)) (PreH9 : (q_pre = u_pre)) (PreH10 : (mode_pre = 2)) (PreH11 : (bit_index_pre >= 0)) (PreH12 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH13 : ((Zabs (size)) <= cap)) (PreH14 : (cap >= 0)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (INT_MIN < size) ”
).

Definition mpz_div_q_2exp_partial_solve_wit_2_pure_split_goal_1 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) <= INT_MAX)) (PreH2 : (size <= INT_MAX)) (PreH3 : (mode_pre <= INT_MAX)) (PreH4 : (cap >= INT_MIN)) (PreH5 : ((signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) >= INT_MIN)) (PreH6 : (size >= INT_MIN)) (PreH7 : (mode_pre >= INT_MIN)) (PreH8 : (size <> 0)) (PreH9 : (q_pre = u_pre)) (PreH10 : (mode_pre = 2)) (PreH11 : (bit_index_pre >= 0)) (PreH12 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH13 : ((Zabs (size)) <= cap)) (PreH14 : (cap >= 0)) (PreH15 : (cap <= INT_MAX)) (PreH16 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index_pre)
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (INT_MIN < size) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_2_aux := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (PreH1 : (size <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : ((Zabs (size)) <= cap)) (PreH7 : (cap >= 0)) (PreH8 : (cap <= INT_MAX)) (PreH9 : (same_sign z_eq_trunc size )) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (size <= INT_MAX) ” 
  &&  “ (INT_MIN < size) ” 
  &&  “ (size <> 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_div_q_2exp_partial_solve_wit_2 := mpz_div_q_2exp_partial_solve_wit_2_pure -> mpz_div_q_2exp_partial_solve_wit_2_aux.

Definition mpz_div_q_2exp_partial_solve_wit_3_pure := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) >= 0) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z_eq_trunc size ) ” 
  &&  “ (((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_3_aux := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) >= 0) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z_eq_trunc size ) ” 
  &&  “ (((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ” 
  &&  “ (mode_pre <> 1) ” 
  &&  “ (size > 0) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (size <> 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_div_q_2exp_partial_solve_wit_3 := mpz_div_q_2exp_partial_solve_wit_3_pure -> mpz_div_q_2exp_partial_solve_wit_3_aux.

Definition mpz_div_q_2exp_partial_solve_wit_4_pure := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> (bit_index_pre % ( 32 ) ))
  **  ((( &( "un" ) )) # Int  |-> size)
  **  ((( &( "qn" ) )) # Int  |-> (retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ))
  **  ((( &( "limb_cnt" ) )) # Int  |-> (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)))
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |-> 0)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) >= 0) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z_eq_trunc size ) ” 
  &&  “ (((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_4_aux := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) >= 0) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (same_sign z_eq_trunc size ) ” 
  &&  “ (((Zabs (size)) - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= INT_MAX) ” 
  &&  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) > 0) ” 
  &&  “ (mode_pre <> 0) ” 
  &&  “ (size <= 0) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (size <> 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
.

Definition mpz_div_q_2exp_partial_solve_wit_4 := mpz_div_q_2exp_partial_solve_wit_4_pure -> mpz_div_q_2exp_partial_solve_wit_4_aux.

Definition mpz_div_q_2exp_partial_solve_wit_5_pure := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (qn > 0) ” 
  &&  “ ((qn + limb_cnt ) <= INT_MAX) ” 
  &&  “ (1 <= bit_index) ” 
  &&  “ (bit_index < 32) ” 
  &&  “ ((u__mp_d + (limb_cnt * sizeof(UINT))) = (qp + (limb_cnt * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (limb_cnt >= 0) ”
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_size <= INT_MAX)) (PreH3 : (qn <= INT_MAX)) (PreH4 : (limb_cnt <= INT_MAX)) (PreH5 : (adjust <= INT_MAX)) (PreH6 : (un <= INT_MAX)) (PreH7 : (mode_pre <= INT_MAX)) (PreH8 : (u__mp_alloc >= INT_MIN)) (PreH9 : (u__mp_size >= INT_MIN)) (PreH10 : (qn >= INT_MIN)) (PreH11 : (limb_cnt >= INT_MIN)) (PreH12 : (adjust >= INT_MIN)) (PreH13 : (un >= INT_MIN)) (PreH14 : (mode_pre >= INT_MIN)) (PreH15 : (bit_index <> 0)) (PreH16 : (q_pre = u_pre)) (PreH17 : (mode_pre = 2)) (PreH18 : (bit_index_pre >= 0)) (PreH19 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH20 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH21 : (bit_index >= 0)) (PreH22 : (bit_index < 32)) (PreH23 : (un <> 0)) (PreH24 : ((Zabs (un)) <= cap)) (PreH25 : (cap >= 0)) (PreH26 : (cap <= INT_MAX)) (PreH27 : (same_sign z_eq_trunc un )) (PreH28 : (adjust = 0)) (PreH29 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH30 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH31 : (qn > 0)) (PreH32 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH33 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH34 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH35 : (list_within_bound UINT_MOD l )) (PreH36 : ((last (l) (1)) >= 1)) (PreH37 : (u__mp_size = un)) (PreH38 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH39 : (u__mp_d = qp)) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (limb_cnt >= 0) ”
).

Definition mpz_div_q_2exp_partial_solve_wit_5_pure_split_goal_1 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_size <= INT_MAX)) (PreH3 : (qn <= INT_MAX)) (PreH4 : (limb_cnt <= INT_MAX)) (PreH5 : (adjust <= INT_MAX)) (PreH6 : (un <= INT_MAX)) (PreH7 : (mode_pre <= INT_MAX)) (PreH8 : (u__mp_alloc >= INT_MIN)) (PreH9 : (u__mp_size >= INT_MIN)) (PreH10 : (qn >= INT_MIN)) (PreH11 : (limb_cnt >= INT_MIN)) (PreH12 : (adjust >= INT_MIN)) (PreH13 : (un >= INT_MIN)) (PreH14 : (mode_pre >= INT_MIN)) (PreH15 : (bit_index <> 0)) (PreH16 : (q_pre = u_pre)) (PreH17 : (mode_pre = 2)) (PreH18 : (bit_index_pre >= 0)) (PreH19 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH20 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH21 : (bit_index >= 0)) (PreH22 : (bit_index < 32)) (PreH23 : (un <> 0)) (PreH24 : ((Zabs (un)) <= cap)) (PreH25 : (cap >= 0)) (PreH26 : (cap <= INT_MAX)) (PreH27 : (same_sign z_eq_trunc un )) (PreH28 : (adjust = 0)) (PreH29 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH30 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH31 : (qn > 0)) (PreH32 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH33 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH34 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH35 : (list_within_bound UINT_MOD l )) (PreH36 : ((last (l) (1)) >= 1)) (PreH37 : (u__mp_size = un)) (PreH38 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH39 : (u__mp_d = qp)) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (limb_cnt >= 0) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_5_aux := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index <> 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (qn > 0) ” 
  &&  “ ((qn + limb_cnt ) <= INT_MAX) ” 
  &&  “ (1 <= bit_index) ” 
  &&  “ (bit_index < 32) ” 
  &&  “ ((u__mp_d + (limb_cnt * sizeof(UINT))) = (qp + (limb_cnt * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (limb_cnt >= 0) ” 
  &&  “ (bit_index <> 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ” 
  &&  “ (bit_index >= 0) ” 
  &&  “ (bit_index < 32) ” 
  &&  “ (un <> 0) ” 
  &&  “ ((Zabs (un)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc un ) ” 
  &&  “ (adjust = 0) ” 
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ” 
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ” 
  &&  “ (qn > 0) ” 
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_size = un) ” 
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ” 
  &&  “ (u__mp_d = qp) ”
  &&  (UIntArray.full qp (qn + limb_cnt ) l )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_5 := mpz_div_q_2exp_partial_solve_wit_5_pure -> mpz_div_q_2exp_partial_solve_wit_5_aux.

Definition mpz_div_q_2exp_partial_solve_wit_6 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l_out)) = qn)) (PreH2 : (list_within_bound UINT_MOD l_out )) (PreH3 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH4 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH5 : (bit_index <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH11 : (bit_index >= 0)) (PreH12 : (bit_index < 32)) (PreH13 : (un <> 0)) (PreH14 : ((Zabs (un)) <= cap)) (PreH15 : (cap >= 0)) (PreH16 : (cap <= INT_MAX)) (PreH17 : (same_sign z_eq_trunc un )) (PreH18 : (adjust = 0)) (PreH19 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH20 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH21 : (qn > 0)) (PreH22 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH23 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH24 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH25 : (list_within_bound UINT_MOD l )) (PreH26 : ((last (l) (1)) >= 1)) (PreH27 : (u__mp_size = un)) (PreH28 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH29 : (u__mp_d = qp)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((Zlength (l_out)) = qn) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) )) ” 
  &&  “ (bit_index <> 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ” 
  &&  “ (bit_index >= 0) ” 
  &&  “ (bit_index < 32) ” 
  &&  “ (un <> 0) ” 
  &&  “ ((Zabs (un)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc un ) ” 
  &&  “ (adjust = 0) ” 
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ” 
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ” 
  &&  “ (qn > 0) ” 
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_size = un) ” 
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ” 
  &&  “ (u__mp_d = qp) ”
  &&  (((qp + ((qn - 1 ) * sizeof(UINT)))) # UInt  |-> (Znth ((qn - 1 ) - 0 ) l_out 0))
  **  (UIntArray.missing_i qp (qn - 1 ) 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_7_pure := 
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (qn >= 0) ” 
  &&  “ ((qn + limb_cnt ) <= INT_MAX) ” 
  &&  “ ((u__mp_d + (limb_cnt * sizeof(UINT))) = (qp + (limb_cnt * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (limb_cnt >= 0) ”
) \/
(
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_size <= INT_MAX)) (PreH3 : (qn <= INT_MAX)) (PreH4 : (limb_cnt <= INT_MAX)) (PreH5 : (adjust <= INT_MAX)) (PreH6 : (un <= INT_MAX)) (PreH7 : (mode_pre <= INT_MAX)) (PreH8 : (u__mp_alloc >= INT_MIN)) (PreH9 : (u__mp_size >= INT_MIN)) (PreH10 : (qn >= INT_MIN)) (PreH11 : (limb_cnt >= INT_MIN)) (PreH12 : (adjust >= INT_MIN)) (PreH13 : (un >= INT_MIN)) (PreH14 : (mode_pre >= INT_MIN)) (PreH15 : (bit_index = 0)) (PreH16 : (q_pre = u_pre)) (PreH17 : (mode_pre = 2)) (PreH18 : (bit_index_pre >= 0)) (PreH19 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH20 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH21 : (bit_index >= 0)) (PreH22 : (bit_index < 32)) (PreH23 : (un <> 0)) (PreH24 : ((Zabs (un)) <= cap)) (PreH25 : (cap >= 0)) (PreH26 : (cap <= INT_MAX)) (PreH27 : (same_sign z_eq_trunc un )) (PreH28 : (adjust = 0)) (PreH29 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH30 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH31 : (qn > 0)) (PreH32 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH33 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH34 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH35 : (list_within_bound UINT_MOD l )) (PreH36 : ((last (l) (1)) >= 1)) (PreH37 : (u__mp_size = un)) (PreH38 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH39 : (u__mp_d = qp)) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (limb_cnt >= 0) ”
).

Definition mpz_div_q_2exp_partial_solve_wit_7_pure_split_goal_1 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (u__mp_alloc <= INT_MAX)) (PreH2 : (u__mp_size <= INT_MAX)) (PreH3 : (qn <= INT_MAX)) (PreH4 : (limb_cnt <= INT_MAX)) (PreH5 : (adjust <= INT_MAX)) (PreH6 : (un <= INT_MAX)) (PreH7 : (mode_pre <= INT_MAX)) (PreH8 : (u__mp_alloc >= INT_MIN)) (PreH9 : (u__mp_size >= INT_MIN)) (PreH10 : (qn >= INT_MIN)) (PreH11 : (limb_cnt >= INT_MIN)) (PreH12 : (adjust >= INT_MIN)) (PreH13 : (un >= INT_MIN)) (PreH14 : (mode_pre >= INT_MIN)) (PreH15 : (bit_index = 0)) (PreH16 : (q_pre = u_pre)) (PreH17 : (mode_pre = 2)) (PreH18 : (bit_index_pre >= 0)) (PreH19 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH20 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH21 : (bit_index >= 0)) (PreH22 : (bit_index < 32)) (PreH23 : (un <> 0)) (PreH24 : ((Zabs (un)) <= cap)) (PreH25 : (cap >= 0)) (PreH26 : (cap <= INT_MAX)) (PreH27 : (same_sign z_eq_trunc un )) (PreH28 : (adjust = 0)) (PreH29 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH30 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH31 : (qn > 0)) (PreH32 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH33 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH34 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH35 : (list_within_bound UINT_MOD l )) (PreH36 : ((last (l) (1)) >= 1)) (PreH37 : (u__mp_size = un)) (PreH38 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH39 : (u__mp_d = qp)) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "bit_index" ) )) # UInt64  |-> bit_index)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  ((( &( "adjust" ) )) # Int  |-> adjust)
  **  ((( &( "limb_cnt" ) )) # Int  |-> limb_cnt)
  **  ((( &( "qn" ) )) # Int  |-> qn)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  ((( &( "qp" ) )) # Ptr  |-> qp)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (limb_cnt >= 0) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_7_aux := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.full qp (qn + limb_cnt ) l )
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (qn >= 0) ” 
  &&  “ ((qn + limb_cnt ) <= INT_MAX) ” 
  &&  “ ((u__mp_d + (limb_cnt * sizeof(UINT))) = (qp + (limb_cnt * sizeof(UINT)))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ (limb_cnt >= 0) ” 
  &&  “ (bit_index = 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ” 
  &&  “ (bit_index >= 0) ” 
  &&  “ (bit_index < 32) ” 
  &&  “ (un <> 0) ” 
  &&  “ ((Zabs (un)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc un ) ” 
  &&  “ (adjust = 0) ” 
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ” 
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ” 
  &&  “ (qn > 0) ” 
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_size = un) ” 
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ” 
  &&  “ (u__mp_d = qp) ”
  &&  (UIntArray.full qp (qn + limb_cnt ) l )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_7 := mpz_div_q_2exp_partial_solve_wit_7_pure -> mpz_div_q_2exp_partial_solve_wit_7_aux.

Definition mpz_div_q_2exp_partial_solve_wit_8 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 1)) (PreH3 : (size > 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0) ” 
  &&  “ (mode_pre <> 1) ” 
  &&  “ (size > 0) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (size <> 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_div_q_2exp_partial_solve_wit_9 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (ptr: Z) (size: Z) (cap: Z) (retval: Z) (PreH1 : ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0)) (PreH2 : (mode_pre <> 0)) (PreH3 : (size <= 0)) (PreH4 : (retval = (Zabs (size)))) (PreH5 : (size <> 0)) (PreH6 : (q_pre = u_pre)) (PreH7 : (mode_pre = 2)) (PreH8 : (bit_index_pre >= 0)) (PreH9 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH10 : ((Zabs (size)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc size )) ,
  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
|--
  “ ((retval - (signed_last_nbits ((bit_index_pre ÷ 32 )) (32)) ) <= 0) ” 
  &&  “ (mode_pre <> 0) ” 
  &&  “ (size <= 0) ” 
  &&  “ (retval = (Zabs (size))) ” 
  &&  “ (size <> 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ ((Zabs (size)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc size ) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> cap)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> ptr)
  **  (mpd_store_Z_compact UINT_MOD ptr (Zabs (z_eq_trunc)) (Zabs (size)) )
  **  (UIntArray.undef_seg ptr (Zabs (size)) cap )
.

Definition mpz_div_q_2exp_partial_solve_wit_10 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((Znth ((qn - 1 ) - 0 ) l_out 0) <> 0) ” 
  &&  “ ((Zlength (l_out)) = qn) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) )) ” 
  &&  “ (bit_index <> 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ” 
  &&  “ (bit_index >= 0) ” 
  &&  “ (bit_index < 32) ” 
  &&  “ (un <> 0) ” 
  &&  “ ((Zabs (un)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc un ) ” 
  &&  “ (adjust = 0) ” 
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ” 
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ” 
  &&  “ (qn > 0) ” 
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_size = un) ” 
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ” 
  &&  “ (u__mp_d = qp) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_11 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (l_out: (@list Z)) (retval: Z) (PreH1 : ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0)) (PreH2 : ((Zlength (l_out)) = qn)) (PreH3 : (list_within_bound UINT_MOD l_out )) (PreH4 : (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32)))) (PreH5 : ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) ))) (PreH6 : (bit_index <> 0)) (PreH7 : (q_pre = u_pre)) (PreH8 : (mode_pre = 2)) (PreH9 : (bit_index_pre >= 0)) (PreH10 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH11 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH12 : (bit_index >= 0)) (PreH13 : (bit_index < 32)) (PreH14 : (un <> 0)) (PreH15 : ((Zabs (un)) <= cap)) (PreH16 : (cap >= 0)) (PreH17 : (cap <= INT_MAX)) (PreH18 : (same_sign z_eq_trunc un )) (PreH19 : (adjust = 0)) (PreH20 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH21 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH22 : (qn > 0)) (PreH23 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH24 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH25 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH26 : (list_within_bound UINT_MOD l )) (PreH27 : ((last (l) (1)) >= 1)) (PreH28 : (u__mp_size = un)) (PreH29 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH30 : (u__mp_d = qp)) ,
  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ ((Znth ((qn - 1 ) - 0 ) l_out 0) = 0) ” 
  &&  “ ((Zlength (l_out)) = qn) ” 
  &&  “ (list_within_bound UINT_MOD l_out ) ” 
  &&  “ (retval = (unsigned_last_nbits (((Znth (limb_cnt) (l) (0)) * (Z.pow (2) ((32 - bit_index ))) )) (32))) ” 
  &&  “ ((list_to_Z (UINT_MOD) ((sublist (limb_cnt) ((limb_cnt + qn )) (l)))) = (((list_to_Z (UINT_MOD) (l_out)) * (Z.pow (2) (bit_index)) ) + (retval ÷ (Z.pow (2) ((32 - bit_index ))) ) )) ” 
  &&  “ (bit_index <> 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ” 
  &&  “ (bit_index >= 0) ” 
  &&  “ (bit_index < 32) ” 
  &&  “ (un <> 0) ” 
  &&  “ ((Zabs (un)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc un ) ” 
  &&  “ (adjust = 0) ” 
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ” 
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ” 
  &&  “ (qn > 0) ” 
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_size = un) ” 
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ” 
  &&  “ (u__mp_d = qp) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.seg qp 0 qn l_out )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_12 := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (bit_index: Z) (un: Z) (adjust: Z) (limb_cnt: Z) (qn: Z) (u__mp_size: Z) (u__mp_alloc: Z) (u__mp_d: Z) (qp: Z) (l: (@list Z)) (cap: Z) (PreH1 : (bit_index = 0)) (PreH2 : (q_pre = u_pre)) (PreH3 : (mode_pre = 2)) (PreH4 : (bit_index_pre >= 0)) (PreH5 : ((bit_index_pre ÷ 32 ) <= INT_MAX)) (PreH6 : (bit_index = (bit_index_pre % ( 32 ) ))) (PreH7 : (bit_index >= 0)) (PreH8 : (bit_index < 32)) (PreH9 : (un <> 0)) (PreH10 : ((Zabs (un)) <= cap)) (PreH11 : (cap >= 0)) (PreH12 : (cap <= INT_MAX)) (PreH13 : (same_sign z_eq_trunc un )) (PreH14 : (adjust = 0)) (PreH15 : (limb_cnt = (bit_index_pre ÷ 32 ))) (PreH16 : (qn = ((Zabs (un)) - limb_cnt ))) (PreH17 : (qn > 0)) (PreH18 : ((qn + limb_cnt ) = (Zabs (un)))) (PreH19 : ((Zlength (l)) = (qn + limb_cnt ))) (PreH20 : ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc)))) (PreH21 : (list_within_bound UINT_MOD l )) (PreH22 : ((last (l) (1)) >= 1)) (PreH23 : (u__mp_size = un)) (PreH24 : (u__mp_alloc = (Z.max (qn) (cap)))) (PreH25 : (u__mp_d = qp)) ,
  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |-> u__mp_size)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
|--
  “ (bit_index = 0) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (mode_pre = 2) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ ((bit_index_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ (bit_index = (bit_index_pre % ( 32 ) )) ” 
  &&  “ (bit_index >= 0) ” 
  &&  “ (bit_index < 32) ” 
  &&  “ (un <> 0) ” 
  &&  “ ((Zabs (un)) <= cap) ” 
  &&  “ (cap >= 0) ” 
  &&  “ (cap <= INT_MAX) ” 
  &&  “ (same_sign z_eq_trunc un ) ” 
  &&  “ (adjust = 0) ” 
  &&  “ (limb_cnt = (bit_index_pre ÷ 32 )) ” 
  &&  “ (qn = ((Zabs (un)) - limb_cnt )) ” 
  &&  “ (qn > 0) ” 
  &&  “ ((qn + limb_cnt ) = (Zabs (un))) ” 
  &&  “ ((Zlength (l)) = (qn + limb_cnt )) ” 
  &&  “ ((list_to_Z (UINT_MOD) (l)) = (Zabs (z_eq_trunc))) ” 
  &&  “ (list_within_bound UINT_MOD l ) ” 
  &&  “ ((last (l) (1)) >= 1) ” 
  &&  “ (u__mp_size = un) ” 
  &&  “ (u__mp_alloc = (Z.max (qn) (cap))) ” 
  &&  “ (u__mp_d = qp) ”
  &&  ((&((q_pre)  # "__mpz_struct" ->ₛ "_mp_size")) # Int  |->_)
  **  (UIntArray.seg qp 0 qn (sublist (limb_cnt) ((limb_cnt + qn )) (l)) )
  **  (UIntArray.seg qp qn (qn + limb_cnt ) (sublist (qn) ((qn + limb_cnt )) (l)) )
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_alloc")) # Int  |-> u__mp_alloc)
  **  ((&((u_pre)  # "__mpz_struct" ->ₛ "_mp_d")) # Ptr  |-> u__mp_d)
  **  (UIntArray.undef_seg qp (qn + limb_cnt ) (Z.max (qn) (cap)) )
.

Definition mpz_div_q_2exp_partial_solve_wit_13_pure := 
forall (mode_pre: Z) (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (un: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (bit_index_pre >= 0)) (PreH3 : (un < 0)) (PreH4 : (same_sign z_eq_trunc un )) ,
  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "mode" ) )) # Int  |-> mode_pre)
  **  ((( &( "un" ) )) # Int  |-> un)
  **  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
  **  ((( &( "bit_index" ) )) # UInt64  |->_)
  **  ((( &( "qn" ) )) # Int  |->_)
  **  ((( &( "limb_cnt" ) )) # Int  |->_)
  **  ((( &( "qp" ) )) # Ptr  |->_)
  **  ((( &( "adjust" ) )) # Int  |->_)
|--
  “ (q_pre = q_pre) ”
.

Definition mpz_div_q_2exp_partial_solve_wit_13_aux := 
forall (bit_index_pre: Z) (u_pre: Z) (q_pre: Z) (z_eq_trunc: Z) (un: Z) (PreH1 : (q_pre = u_pre)) (PreH2 : (bit_index_pre >= 0)) (PreH3 : (un < 0)) (PreH4 : (same_sign z_eq_trunc un )) ,
  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
|--
  “ (q_pre = q_pre) ” 
  &&  “ (q_pre = u_pre) ” 
  &&  “ (bit_index_pre >= 0) ” 
  &&  “ (un < 0) ” 
  &&  “ (same_sign z_eq_trunc un ) ”
  &&  (store_Z q_pre (Z.quot ((Zabs (z_eq_trunc))) ((Z.pow (2) (bit_index_pre)))) )
.

Definition mpz_div_q_2exp_partial_solve_wit_13 := mpz_div_q_2exp_partial_solve_wit_13_pure -> mpz_div_q_2exp_partial_solve_wit_13_aux.

(*----- Function mpz_tdiv_q_2exp -----*)

Definition mpz_tdiv_q_2exp_safety_wit_1 := 
forall (cnt_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (cnt_pre >= 0)) (PreH3 : ((cnt_pre ÷ 32 ) <= INT_MAX)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "cnt" ) )) # UInt64  |-> cnt_pre)
  **  (store_Z r_pre z_eq )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition mpz_tdiv_q_2exp_return_wit_1 := 
forall (cnt_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (r_pre = u_pre)) (PreH3 : (cnt_pre >= 0)) (PreH4 : ((cnt_pre ÷ 32 ) <= INT_MAX)) ,
  (store_Z r_pre (Z.quot (z_eq) ((Z.pow (2) (cnt_pre)))) )
|--
  “ (r_pre = u_pre) ”
  &&  (store_Z r_pre (Z.quot (z_eq) ((Z.pow (2) (cnt_pre)))) )
.

Definition mpz_tdiv_q_2exp_partial_solve_wit_1_pure := 
forall (cnt_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (cnt_pre >= 0)) (PreH3 : ((cnt_pre ÷ 32 ) <= INT_MAX)) ,
  ((( &( "r" ) )) # Ptr  |-> r_pre)
  **  ((( &( "u" ) )) # Ptr  |-> u_pre)
  **  ((( &( "cnt" ) )) # UInt64  |-> cnt_pre)
  **  (store_Z r_pre z_eq )
|--
  “ (r_pre = u_pre) ” 
  &&  “ (2 = 2) ” 
  &&  “ (cnt_pre >= 0) ” 
  &&  “ ((cnt_pre ÷ 32 ) <= INT_MAX) ”
.

Definition mpz_tdiv_q_2exp_partial_solve_wit_1_aux := 
forall (cnt_pre: Z) (u_pre: Z) (r_pre: Z) (z_eq: Z) (PreH1 : (r_pre = u_pre)) (PreH2 : (cnt_pre >= 0)) (PreH3 : ((cnt_pre ÷ 32 ) <= INT_MAX)) ,
  (store_Z r_pre z_eq )
|--
  “ (r_pre = u_pre) ” 
  &&  “ (2 = 2) ” 
  &&  “ (cnt_pre >= 0) ” 
  &&  “ ((cnt_pre ÷ 32 ) <= INT_MAX) ” 
  &&  “ (r_pre = u_pre) ” 
  &&  “ (cnt_pre >= 0) ” 
  &&  “ ((cnt_pre ÷ 32 ) <= INT_MAX) ”
  &&  (store_Z r_pre z_eq )
.

Definition mpz_tdiv_q_2exp_partial_solve_wit_1 := mpz_tdiv_q_2exp_partial_solve_wit_1_pure -> mpz_tdiv_q_2exp_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include gmp_Strategy_Correct.
Include gmp_optional_Strategy_Correct.

Axiom proof_of_mpn_copyi_safety_wit_1 : mpn_copyi_safety_wit_1.
Axiom proof_of_mpn_copyi_safety_wit_2_off_zero : mpn_copyi_safety_wit_2_off_zero.
Axiom proof_of_mpn_copyi_safety_wit_3_off_pos : mpn_copyi_safety_wit_3_off_pos.
Axiom proof_of_mpn_copyi_safety_wit_4_off_zero : mpn_copyi_safety_wit_4_off_zero.
Axiom proof_of_mpn_copyi_safety_wit_5_off_pos : mpn_copyi_safety_wit_5_off_pos.
Axiom proof_of_mpn_copyi_entail_wit_1_off_zero : mpn_copyi_entail_wit_1_off_zero.
Axiom proof_of_mpn_copyi_entail_wit_2_off_pos : mpn_copyi_entail_wit_2_off_pos.
Axiom proof_of_mpn_copyi_entail_wit_3_off_zero : mpn_copyi_entail_wit_3_off_zero.
Axiom proof_of_mpn_copyi_entail_wit_4_off_pos : mpn_copyi_entail_wit_4_off_pos.
Axiom proof_of_mpn_copyi_entail_wit_5_off_zero : mpn_copyi_entail_wit_5_off_zero.
Axiom proof_of_mpn_copyi_entail_wit_6_off_pos : mpn_copyi_entail_wit_6_off_pos.
Axiom proof_of_mpn_copyi_return_wit_1_off_zero : mpn_copyi_return_wit_1_off_zero.
Axiom proof_of_mpn_copyi_return_wit_2_off_pos : mpn_copyi_return_wit_2_off_pos.
Axiom proof_of_mpn_copyi_partial_solve_wit_1_off_zero_pure : mpn_copyi_partial_solve_wit_1_off_zero_pure.
Axiom proof_of_mpn_copyi_partial_solve_wit_1_off_zero : mpn_copyi_partial_solve_wit_1_off_zero.
Axiom proof_of_mpn_copyi_partial_solve_wit_2_off_pos_pure : mpn_copyi_partial_solve_wit_2_off_pos_pure.
Axiom proof_of_mpn_copyi_partial_solve_wit_2_off_pos : mpn_copyi_partial_solve_wit_2_off_pos.
Axiom proof_of_mpn_copyi_partial_solve_wit_3_off_zero : mpn_copyi_partial_solve_wit_3_off_zero.
Axiom proof_of_mpn_copyi_partial_solve_wit_4_off_zero : mpn_copyi_partial_solve_wit_4_off_zero.
Axiom proof_of_mpn_copyi_partial_solve_wit_5_off_pos : mpn_copyi_partial_solve_wit_5_off_pos.
Axiom proof_of_mpn_copyi_partial_solve_wit_6_off_pos : mpn_copyi_partial_solve_wit_6_off_pos.
Axiom proof_of_mpn_copyi_which_implies_wit_1 : mpn_copyi_which_implies_wit_1.
Axiom proof_of_mpn_copyi_which_implies_wit_2 : mpn_copyi_which_implies_wit_2.
Axiom proof_of_mpn_rshift_safety_wit_1 : mpn_rshift_safety_wit_1.
Axiom proof_of_mpn_rshift_safety_wit_2 : mpn_rshift_safety_wit_2.
Axiom proof_of_mpn_rshift_safety_wit_3 : mpn_rshift_safety_wit_3.
Axiom proof_of_mpn_rshift_safety_wit_4 : mpn_rshift_safety_wit_4.
Axiom proof_of_mpn_rshift_safety_wit_5 : mpn_rshift_safety_wit_5.
Axiom proof_of_mpn_rshift_safety_wit_6 : mpn_rshift_safety_wit_6.
Axiom proof_of_mpn_rshift_safety_wit_7 : mpn_rshift_safety_wit_7.
Axiom proof_of_mpn_rshift_safety_wit_8 : mpn_rshift_safety_wit_8.
Axiom proof_of_mpn_rshift_safety_wit_9 : mpn_rshift_safety_wit_9.
Axiom proof_of_mpn_rshift_safety_wit_10 : mpn_rshift_safety_wit_10.
Axiom proof_of_mpn_rshift_safety_wit_11 : mpn_rshift_safety_wit_11.
Axiom proof_of_mpn_rshift_safety_wit_12 : mpn_rshift_safety_wit_12.
Axiom proof_of_mpn_rshift_entail_wit_1 : mpn_rshift_entail_wit_1.
Axiom proof_of_mpn_rshift_entail_wit_2 : mpn_rshift_entail_wit_2.
Axiom proof_of_mpn_rshift_entail_wit_3 : mpn_rshift_entail_wit_3.
Axiom proof_of_mpn_rshift_entail_wit_4 : mpn_rshift_entail_wit_4.
Axiom proof_of_mpn_rshift_entail_wit_5 : mpn_rshift_entail_wit_5.
Axiom proof_of_mpn_rshift_entail_wit_6 : mpn_rshift_entail_wit_6.
Axiom proof_of_mpn_rshift_entail_wit_7 : mpn_rshift_entail_wit_7.
Axiom proof_of_mpn_rshift_return_wit_1 : mpn_rshift_return_wit_1.
Axiom proof_of_mpn_rshift_partial_solve_wit_1_pure : mpn_rshift_partial_solve_wit_1_pure.
Axiom proof_of_mpn_rshift_partial_solve_wit_1 : mpn_rshift_partial_solve_wit_1.
Axiom proof_of_mpn_rshift_partial_solve_wit_2 : mpn_rshift_partial_solve_wit_2.
Axiom proof_of_mpn_rshift_partial_solve_wit_3 : mpn_rshift_partial_solve_wit_3.
Axiom proof_of_mpn_rshift_partial_solve_wit_4 : mpn_rshift_partial_solve_wit_4.
Axiom proof_of_mpn_rshift_partial_solve_wit_5 : mpn_rshift_partial_solve_wit_5.
Axiom proof_of_mpn_rshift_which_implies_wit_1 : mpn_rshift_which_implies_wit_1.
Axiom proof_of_mpz_div_q_2exp_safety_wit_1 : mpz_div_q_2exp_safety_wit_1.
Axiom proof_of_mpz_div_q_2exp_safety_wit_2 : mpz_div_q_2exp_safety_wit_2.
Axiom proof_of_mpz_div_q_2exp_safety_wit_3 : mpz_div_q_2exp_safety_wit_3.
Axiom proof_of_mpz_div_q_2exp_safety_wit_4 : mpz_div_q_2exp_safety_wit_4.
Axiom proof_of_mpz_div_q_2exp_safety_wit_5 : mpz_div_q_2exp_safety_wit_5.
Axiom proof_of_mpz_div_q_2exp_safety_wit_6 : mpz_div_q_2exp_safety_wit_6.
Axiom proof_of_mpz_div_q_2exp_safety_wit_7 : mpz_div_q_2exp_safety_wit_7.
Axiom proof_of_mpz_div_q_2exp_safety_wit_8 : mpz_div_q_2exp_safety_wit_8.
Axiom proof_of_mpz_div_q_2exp_safety_wit_9 : mpz_div_q_2exp_safety_wit_9.
Axiom proof_of_mpz_div_q_2exp_safety_wit_10 : mpz_div_q_2exp_safety_wit_10.
Axiom proof_of_mpz_div_q_2exp_safety_wit_11 : mpz_div_q_2exp_safety_wit_11.
Axiom proof_of_mpz_div_q_2exp_safety_wit_12 : mpz_div_q_2exp_safety_wit_12.
Axiom proof_of_mpz_div_q_2exp_safety_wit_13 : mpz_div_q_2exp_safety_wit_13.
Axiom proof_of_mpz_div_q_2exp_safety_wit_14 : mpz_div_q_2exp_safety_wit_14.
Axiom proof_of_mpz_div_q_2exp_safety_wit_15 : mpz_div_q_2exp_safety_wit_15.
Axiom proof_of_mpz_div_q_2exp_safety_wit_16 : mpz_div_q_2exp_safety_wit_16.
Axiom proof_of_mpz_div_q_2exp_safety_wit_17 : mpz_div_q_2exp_safety_wit_17.
Axiom proof_of_mpz_div_q_2exp_safety_wit_18 : mpz_div_q_2exp_safety_wit_18.
Axiom proof_of_mpz_div_q_2exp_safety_wit_19 : mpz_div_q_2exp_safety_wit_19.
Axiom proof_of_mpz_div_q_2exp_safety_wit_20 : mpz_div_q_2exp_safety_wit_20.
Axiom proof_of_mpz_div_q_2exp_safety_wit_21 : mpz_div_q_2exp_safety_wit_21.
Axiom proof_of_mpz_div_q_2exp_safety_wit_22 : mpz_div_q_2exp_safety_wit_22.
Axiom proof_of_mpz_div_q_2exp_safety_wit_23 : mpz_div_q_2exp_safety_wit_23.
Axiom proof_of_mpz_div_q_2exp_safety_wit_24 : mpz_div_q_2exp_safety_wit_24.
Axiom proof_of_mpz_div_q_2exp_safety_wit_25 : mpz_div_q_2exp_safety_wit_25.
Axiom proof_of_mpz_div_q_2exp_safety_wit_26 : mpz_div_q_2exp_safety_wit_26.
Axiom proof_of_mpz_div_q_2exp_safety_wit_27 : mpz_div_q_2exp_safety_wit_27.
Axiom proof_of_mpz_div_q_2exp_safety_wit_28 : mpz_div_q_2exp_safety_wit_28.
Axiom proof_of_mpz_div_q_2exp_safety_wit_29 : mpz_div_q_2exp_safety_wit_29.
Axiom proof_of_mpz_div_q_2exp_safety_wit_30 : mpz_div_q_2exp_safety_wit_30.
Axiom proof_of_mpz_div_q_2exp_safety_wit_31 : mpz_div_q_2exp_safety_wit_31.
Axiom proof_of_mpz_div_q_2exp_safety_wit_32 : mpz_div_q_2exp_safety_wit_32.
Axiom proof_of_mpz_div_q_2exp_safety_wit_33 : mpz_div_q_2exp_safety_wit_33.
Axiom proof_of_mpz_div_q_2exp_safety_wit_34 : mpz_div_q_2exp_safety_wit_34.
Axiom proof_of_mpz_div_q_2exp_entail_wit_1 : mpz_div_q_2exp_entail_wit_1.
Axiom proof_of_mpz_div_q_2exp_entail_wit_2_1 : mpz_div_q_2exp_entail_wit_2_1.
Axiom proof_of_mpz_div_q_2exp_entail_wit_2_2 : mpz_div_q_2exp_entail_wit_2_2.
Axiom proof_of_mpz_div_q_2exp_entail_wit_3_1 : mpz_div_q_2exp_entail_wit_3_1.
Axiom proof_of_mpz_div_q_2exp_entail_wit_3_2 : mpz_div_q_2exp_entail_wit_3_2.
Axiom proof_of_mpz_div_q_2exp_entail_wit_3_3 : mpz_div_q_2exp_entail_wit_3_3.
Axiom proof_of_mpz_div_q_2exp_entail_wit_3_4 : mpz_div_q_2exp_entail_wit_3_4.
Axiom proof_of_mpz_div_q_2exp_return_wit_1 : mpz_div_q_2exp_return_wit_1.
Axiom proof_of_mpz_div_q_2exp_return_wit_2 : mpz_div_q_2exp_return_wit_2.
Axiom proof_of_mpz_div_q_2exp_return_wit_3 : mpz_div_q_2exp_return_wit_3.
Axiom proof_of_mpz_div_q_2exp_return_wit_4 : mpz_div_q_2exp_return_wit_4.
Axiom proof_of_mpz_div_q_2exp_return_wit_5 : mpz_div_q_2exp_return_wit_5.
Axiom proof_of_mpz_div_q_2exp_return_wit_6 : mpz_div_q_2exp_return_wit_6.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_1 : mpz_div_q_2exp_partial_solve_wit_1.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_2_pure : mpz_div_q_2exp_partial_solve_wit_2_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_2 : mpz_div_q_2exp_partial_solve_wit_2.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_3_pure : mpz_div_q_2exp_partial_solve_wit_3_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_3 : mpz_div_q_2exp_partial_solve_wit_3.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_4_pure : mpz_div_q_2exp_partial_solve_wit_4_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_4 : mpz_div_q_2exp_partial_solve_wit_4.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_5_pure : mpz_div_q_2exp_partial_solve_wit_5_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_5 : mpz_div_q_2exp_partial_solve_wit_5.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_6 : mpz_div_q_2exp_partial_solve_wit_6.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_7_pure : mpz_div_q_2exp_partial_solve_wit_7_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_7 : mpz_div_q_2exp_partial_solve_wit_7.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_8 : mpz_div_q_2exp_partial_solve_wit_8.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_9 : mpz_div_q_2exp_partial_solve_wit_9.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_10 : mpz_div_q_2exp_partial_solve_wit_10.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_11 : mpz_div_q_2exp_partial_solve_wit_11.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_12 : mpz_div_q_2exp_partial_solve_wit_12.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_13_pure : mpz_div_q_2exp_partial_solve_wit_13_pure.
Axiom proof_of_mpz_div_q_2exp_partial_solve_wit_13 : mpz_div_q_2exp_partial_solve_wit_13.
Axiom proof_of_mpz_tdiv_q_2exp_safety_wit_1 : mpz_tdiv_q_2exp_safety_wit_1.
Axiom proof_of_mpz_tdiv_q_2exp_return_wit_1 : mpz_tdiv_q_2exp_return_wit_1.
Axiom proof_of_mpz_tdiv_q_2exp_partial_solve_wit_1_pure : mpz_tdiv_q_2exp_partial_solve_wit_1_pure.
Axiom proof_of_mpz_tdiv_q_2exp_partial_solve_wit_1 : mpz_tdiv_q_2exp_partial_solve_wit_1.

End VC_Correct.
