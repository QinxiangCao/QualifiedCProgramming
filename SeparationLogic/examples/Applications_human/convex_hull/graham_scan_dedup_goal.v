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
Require Import SimpleC.EE.Applications_human.convex_hull.convex_hull_lib.
Require Import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.
From SimpleC.EE.Applications_human.convex_hull Require Import point_array_strategy_goal.
From SimpleC.EE.Applications_human.convex_hull Require Import point_array_strategy_proof.
From SimpleC.EE.Applications_human.convex_hull Require Import safeexec_strategy_goal.
From SimpleC.EE.Applications_human.convex_hull Require Import safeexec_strategy_proof.

(*----- Function leftdown_dedup -----*)

Definition leftdown_dedup_safety_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre < b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition leftdown_dedup_safety_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre < b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition leftdown_dedup_safety_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition leftdown_dedup_safety_wit_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition leftdown_dedup_safety_wit_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition leftdown_dedup_safety_wit_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition leftdown_dedup_safety_wit_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition leftdown_dedup_entail_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition leftdown_dedup_return_wit_1 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  TT && emp 
|--
  “ (0 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  TT && emp 
|--
  “ (0 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition leftdown_dedup_return_wit_1_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  (0 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition leftdown_dedup_return_wit_2 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  TT && emp 
|--
  “ (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  TT && emp 
|--
  “ (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition leftdown_dedup_return_wit_2_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition leftdown_dedup_return_wit_3 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) ,
  TT && emp 
|--
  “ ((-1) = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) ,
  TT && emp 
|--
  “ ((-1) = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition leftdown_dedup_return_wit_3_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) ,
  ((-1) = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition leftdown_dedup_return_wit_4 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) ,
  TT && emp 
|--
  “ (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) ,
  TT && emp 
|--
  “ (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition leftdown_dedup_return_wit_4_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) ,
  (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition leftdown_dedup_return_wit_5 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre < b_x_pre)) ,
  TT && emp 
|--
  “ ((-1) = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre < b_x_pre)) ,
  TT && emp 
|--
  “ ((-1) = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition leftdown_dedup_return_wit_5_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre < b_x_pre)) ,
  ((-1) = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

(*----- Function cross_prod -----*)

Definition cross_prod_safety_wit_1 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) )) ”
).

Definition cross_prod_safety_wit_1_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) ) <= INT_MAX) ”
.

Definition cross_prod_safety_wit_1_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) )) ”
.

Definition cross_prod_safety_wit_2 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) )) ”
).

Definition cross_prod_safety_wit_2_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) <= INT_MAX) ”
.

Definition cross_prod_safety_wit_2_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) )) ”
.

Definition cross_prod_safety_wit_3 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_x_pre - a_x_pre )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_x_pre - a_x_pre )) ”
).

Definition cross_prod_safety_wit_3_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_x_pre - a_x_pre ) <= INT_MAX) ”
.

Definition cross_prod_safety_wit_3_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (c_x_pre - a_x_pre )) ”
.

Definition cross_prod_safety_wit_4 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_y_pre - a_y_pre )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_y_pre - a_y_pre )) ”
).

Definition cross_prod_safety_wit_4_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_y_pre - a_y_pre ) <= INT_MAX) ”
.

Definition cross_prod_safety_wit_4_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (b_y_pre - a_y_pre )) ”
.

Definition cross_prod_safety_wit_5 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) )) ”
).

Definition cross_prod_safety_wit_5_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) <= INT_MAX) ”
.

Definition cross_prod_safety_wit_5_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= ((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) )) ”
.

Definition cross_prod_safety_wit_6 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_y_pre - a_y_pre )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_y_pre - a_y_pre )) ”
).

Definition cross_prod_safety_wit_6_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_y_pre - a_y_pre ) <= INT_MAX) ”
.

Definition cross_prod_safety_wit_6_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (c_y_pre - a_y_pre )) ”
.

Definition cross_prod_safety_wit_7 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_x_pre - a_x_pre )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_x_pre - a_x_pre )) ”
).

Definition cross_prod_safety_wit_7_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_x_pre - a_x_pre ) <= INT_MAX) ”
.

Definition cross_prod_safety_wit_7_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (b_x_pre - a_x_pre )) ”
.

Definition cross_prod_entail_wit_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  TT && emp 
|--
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  emp
.

Definition cross_prod_return_wit_1 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  TT && emp 
|--
  “ ((((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) ) = (point_cross_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (c_x_pre) (c_y_pre))) ”
  &&  emp
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  TT && emp 
|--
  “ ((((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) ) = (point_cross_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (c_x_pre) (c_y_pre))) ”
  &&  emp
).

Definition cross_prod_return_wit_1_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((((b_x_pre - a_x_pre ) * (c_y_pre - a_y_pre ) ) - ((b_y_pre - a_y_pre ) * (c_x_pre - a_x_pre ) ) ) = (point_cross_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (c_x_pre) (c_y_pre)))
.

(*----- Function dot_prod -----*)

Definition dot_prod_safety_wit_1 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) )) ”
).

Definition dot_prod_safety_wit_1_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) ) <= INT_MAX) ”
.

Definition dot_prod_safety_wit_1_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) )) ”
.

Definition dot_prod_safety_wit_2 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) )) ”
).

Definition dot_prod_safety_wit_2_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) <= INT_MAX) ”
.

Definition dot_prod_safety_wit_2_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) )) ”
.

Definition dot_prod_safety_wit_3 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_y_pre - a_y_pre )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_y_pre - a_y_pre )) ”
).

Definition dot_prod_safety_wit_3_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_y_pre - a_y_pre ) <= INT_MAX) ”
.

Definition dot_prod_safety_wit_3_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (c_y_pre - a_y_pre )) ”
.

Definition dot_prod_safety_wit_4 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_y_pre - a_y_pre )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_y_pre - a_y_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_y_pre - a_y_pre )) ”
).

Definition dot_prod_safety_wit_4_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_y_pre - a_y_pre ) <= INT_MAX) ”
.

Definition dot_prod_safety_wit_4_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (b_y_pre - a_y_pre )) ”
.

Definition dot_prod_safety_wit_5 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) )) ”
).

Definition dot_prod_safety_wit_5_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ (((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) <= INT_MAX) ”
.

Definition dot_prod_safety_wit_5_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= ((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) )) ”
.

Definition dot_prod_safety_wit_6 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_x_pre - a_x_pre )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c_x_pre - a_x_pre )) ”
).

Definition dot_prod_safety_wit_6_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((c_x_pre - a_x_pre ) <= INT_MAX) ”
.

Definition dot_prod_safety_wit_6_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (c_x_pre - a_x_pre )) ”
.

Definition dot_prod_safety_wit_7 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_x_pre - a_x_pre )) ”
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_x_pre - a_x_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (b_x_pre - a_x_pre )) ”
).

Definition dot_prod_safety_wit_7_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((b_x_pre - a_x_pre ) <= INT_MAX) ”
.

Definition dot_prod_safety_wit_7_split_goal_2 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "c_x" ) )) # Int  |-> c_x_pre)
  **  ((( &( "c_y" ) )) # Int  |-> c_y_pre)
|--
  “ ((INT_MIN) <= (b_x_pre - a_x_pre )) ”
.

Definition dot_prod_entail_wit_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  TT && emp 
|--
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_x_pre) ” 
  &&  “ (c_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= c_y_pre) ” 
  &&  “ (c_y_pre <= point_bound) ”
  &&  emp
.

Definition dot_prod_return_wit_1 := 
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  TT && emp 
|--
  “ ((((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) ) = (point_dot_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (c_x_pre) (c_y_pre))) ”
  &&  emp
) \/
(
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  TT && emp 
|--
  “ ((((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) ) = (point_dot_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (c_x_pre) (c_y_pre))) ”
  &&  emp
).

Definition dot_prod_return_wit_1_split_goal_1 := 
forall (c_y_pre: Z) (c_x_pre: Z) (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : ((-point_bound) <= a_x_pre)) (PreH2 : (a_x_pre <= point_bound)) (PreH3 : ((-point_bound) <= a_y_pre)) (PreH4 : (a_y_pre <= point_bound)) (PreH5 : ((-point_bound) <= b_x_pre)) (PreH6 : (b_x_pre <= point_bound)) (PreH7 : ((-point_bound) <= b_y_pre)) (PreH8 : (b_y_pre <= point_bound)) (PreH9 : ((-point_bound) <= c_x_pre)) (PreH10 : (c_x_pre <= point_bound)) (PreH11 : ((-point_bound) <= c_y_pre)) (PreH12 : (c_y_pre <= point_bound)) ,
  ((((b_x_pre - a_x_pre ) * (c_x_pre - a_x_pre ) ) + ((b_y_pre - a_y_pre ) * (c_y_pre - a_y_pre ) ) ) = (point_dot_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (c_x_pre) (c_y_pre)))
.

(*----- Function cmp_polar -----*)

Definition cmp_polar_safety_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH2 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH3 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH4 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH5 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_safety_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH3 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH4 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH5 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_safety_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH3 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH4 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH5 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH3 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH4 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH5 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_safety_wit_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH4 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH5 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH6 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH7 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |-> retval)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH2 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH3 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH4 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH5 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH6 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH7 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_safety_wit_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid > 0)) (PreH2 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH3 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH5 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH6 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH7 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH8 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_8 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid <= 0)) (PreH2 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH3 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH5 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH6 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH7 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH8 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_safety_wit_9 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid < 0)) (PreH2 : (mid <= 0)) (PreH3 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_polar_safety_wit_10 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid < 0)) (PreH2 : (mid <= 0)) (PreH3 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_polar_safety_wit_11 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid >= 0)) (PreH2 : (mid <= 0)) (PreH3 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "cr" ) )) # Int  |-> cr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_polar_entail_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH2 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH3 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH4 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
.

Definition cmp_polar_entail_wit_2 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH4 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH5 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH6 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH7 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (retval = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (retval >= 0) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH4 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH5 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH6 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH7 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (retval = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition cmp_polar_entail_wit_2_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH4 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH5 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH6 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH7 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )
.

Definition cmp_polar_entail_wit_2_split_goal_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval >= 0)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH4 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH5 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH6 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH7 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  (retval = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_polar_entail_wit_3 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (retval: Z) (PreH1 : (retval = (point_dot_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (gp_x_pre) (gp_y_pre)))) (PreH2 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH3 : (cr >= 0)) (PreH4 : (cr <= 0)) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (retval = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (retval: Z) (PreH1 : (retval = (point_dot_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (gp_x_pre) (gp_y_pre)))) (PreH2 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH3 : (cr >= 0)) (PreH4 : (cr <= 0)) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (retval = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition cmp_polar_entail_wit_3_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (retval: Z) (PreH1 : (retval = (point_dot_by_value (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre) (gp_x_pre) (gp_y_pre)))) (PreH2 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH3 : (cr >= 0)) (PreH4 : (cr <= 0)) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  (retval = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_polar_return_wit_1 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid >= 0)) (PreH2 : (mid <= 0)) (PreH3 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (0 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid >= 0)) (PreH2 : (mid <= 0)) (PreH3 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (0 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition cmp_polar_return_wit_1_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid >= 0)) (PreH2 : (mid <= 0)) (PreH3 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  (0 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_polar_return_wit_2 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid < 0)) (PreH2 : (mid <= 0)) (PreH3 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid < 0)) (PreH2 : (mid <= 0)) (PreH3 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition cmp_polar_return_wit_2_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid < 0)) (PreH2 : (mid <= 0)) (PreH3 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH5 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH7 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH8 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH9 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_polar_return_wit_3 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid > 0)) (PreH2 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH3 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH5 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH6 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH7 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH8 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid > 0)) (PreH2 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH3 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH5 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH6 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH7 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH8 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition cmp_polar_return_wit_3_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (mid: Z) (cr: Z) (PreH1 : (mid > 0)) (PreH2 : (mid = (point_at_mid ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH3 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH4 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH5 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH6 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH7 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH8 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_polar_return_wit_4 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH4 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH5 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH6 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH7 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH4 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH5 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH6 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH7 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition cmp_polar_return_wit_4_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval < 0)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH4 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH5 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH6 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH7 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  (1 = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_polar_return_wit_5 := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH3 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH4 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH5 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH3 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH4 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH5 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ”
  &&  emp
).

Definition cmp_polar_return_wit_5_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value (gp_x_pre) (gp_y_pre) (a_x_pre) (a_y_pre) (b_x_pre) (b_y_pre)))) (PreH3 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH4 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH5 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH6 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((-1) = (point_cmp_polar ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_polar_partial_solve_wit_1_pure := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH2 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH3 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH4 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (gp_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_y_pre) ” 
  &&  “ (gp_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_x_pre) ”
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ ((-point_bound) <= gp_x_pre) ” 
  &&  “ (gp_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_y_pre) ” 
  &&  “ (gp_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ”
).

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ ((-point_bound) <= gp_x_pre) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (gp_x_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ ((-point_bound) <= gp_y_pre) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (gp_y_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ ((-point_bound) <= a_x_pre) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (a_x_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ ((-point_bound) <= a_y_pre) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_8 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (a_y_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_9 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ ((-point_bound) <= b_x_pre) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_10 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (b_x_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_11 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ ((-point_bound) <= b_y_pre) ”
.

Definition cmp_polar_partial_solve_wit_1_pure_split_goal_12 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (b_y_pre <= INT_MAX)) (PreH2 : (b_x_pre <= INT_MAX)) (PreH3 : (a_y_pre <= INT_MAX)) (PreH4 : (a_x_pre <= INT_MAX)) (PreH5 : (gp_y_pre <= INT_MAX)) (PreH6 : (gp_x_pre <= INT_MAX)) (PreH7 : (b_y_pre >= INT_MIN)) (PreH8 : (b_x_pre >= INT_MIN)) (PreH9 : (a_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (gp_y_pre >= INT_MIN)) (PreH12 : (gp_x_pre >= INT_MIN)) (PreH13 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH14 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH15 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH16 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "cr" ) )) # Int  |->_)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (b_y_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_1_aux := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (PreH1 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH2 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH3 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH4 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (gp_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_y_pre) ” 
  &&  “ (gp_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_x_pre) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
.

Definition cmp_polar_partial_solve_wit_1 := cmp_polar_partial_solve_wit_1_pure -> cmp_polar_partial_solve_wit_1_aux.

Definition cmp_polar_partial_solve_wit_2_pure := 
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH2 : (cr >= 0)) (PreH3 : (cr <= 0)) (PreH4 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH5 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH6 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH7 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH8 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ (gp_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_y_pre) ” 
  &&  “ (gp_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_x_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_x_pre) ”
) \/
(
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_x_pre) ” 
  &&  “ (gp_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_y_pre) ” 
  &&  “ (gp_y_pre <= point_bound) ”
).

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((-point_bound) <= a_x_pre) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ (a_x_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((-point_bound) <= a_y_pre) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ (a_y_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((-point_bound) <= b_x_pre) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ (b_x_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((-point_bound) <= b_y_pre) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_8 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ (b_y_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_9 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((-point_bound) <= gp_x_pre) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_10 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ (gp_x_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_11 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ ((-point_bound) <= gp_y_pre) ”
.

Definition cmp_polar_partial_solve_wit_2_pure_split_goal_12 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (gp_x_pre <= INT_MAX)) (PreH2 : (gp_y_pre <= INT_MAX)) (PreH3 : (a_x_pre <= INT_MAX)) (PreH4 : (a_y_pre <= INT_MAX)) (PreH5 : (b_x_pre <= INT_MAX)) (PreH6 : (b_y_pre <= INT_MAX)) (PreH7 : (cr <= INT_MAX)) (PreH8 : (gp_x_pre >= INT_MIN)) (PreH9 : (gp_y_pre >= INT_MIN)) (PreH10 : (a_x_pre >= INT_MIN)) (PreH11 : (a_y_pre >= INT_MIN)) (PreH12 : (b_x_pre >= INT_MIN)) (PreH13 : (b_y_pre >= INT_MIN)) (PreH14 : (cr >= INT_MIN)) (PreH15 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH16 : (cr >= 0)) (PreH17 : (cr <= 0)) (PreH18 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH19 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH20 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH21 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH22 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "cr" ) )) # Int  |-> cr)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "gp_y" ) )) # Int  |-> gp_y_pre)
  **  ((( &( "gp_x" ) )) # Int  |-> gp_x_pre)
|--
  “ (gp_y_pre <= point_bound) ”
.

Definition cmp_polar_partial_solve_wit_2_aux := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (gp_y_pre: Z) (gp_x_pre: Z) (cr: Z) (PreH1 : (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))) (PreH2 : (cr >= 0)) (PreH3 : (cr <= 0)) (PreH4 : (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) (PreH5 : (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) )) (PreH6 : (point_in_bound (point_mk (a_x_pre) (a_y_pre)) )) (PreH7 : (point_in_bound (point_mk (b_x_pre) (b_y_pre)) )) (PreH8 : (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) )) ,
  TT && emp 
|--
  “ (gp_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_y_pre) ” 
  &&  “ (gp_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= gp_x_pre) ” 
  &&  “ (b_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_y_pre) ” 
  &&  “ (b_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= b_x_pre) ” 
  &&  “ (a_y_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_y_pre) ” 
  &&  “ (a_x_pre <= point_bound) ” 
  &&  “ ((-point_bound) <= a_x_pre) ” 
  &&  “ (cr = (point_cross ((point_mk (gp_x_pre) (gp_y_pre))) ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre))))) ” 
  &&  “ (cr >= 0) ” 
  &&  “ (cr <= 0) ” 
  &&  “ (point_colinear (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (gp_x_pre) (gp_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (a_x_pre) (a_y_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (b_x_pre) (b_y_pre)) ) ” 
  &&  “ (point_polar_cmp_safe_pair (point_mk (gp_x_pre) (gp_y_pre)) (point_mk (a_x_pre) (a_y_pre)) (point_mk (b_x_pre) (b_y_pre)) ) ”
  &&  emp
.

Definition cmp_polar_partial_solve_wit_2 := cmp_polar_partial_solve_wit_2_pure -> cmp_polar_partial_solve_wit_2_aux.

(*----- Function build_hull_from_sorted_tail_dedup -----*)

Definition build_hull_from_sorted_tail_dedup_safety_wit_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (PreH1 : (1 <= tail_n_pre)) (PreH2 : (tail_n_pre < INT_MAX)) (PreH3 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH4 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH5 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH6 : (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) )) (PreH7 : (point_in_bound pivot0_low_level_spec )) (PreH8 : (points_in_bound l_low_level_spec )) (PreH9 : (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec )) ,
  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre 0 (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (0 <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= 0) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_2 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (PreH1 : (1 <= tail_n_pre)) (PreH2 : (tail_n_pre < INT_MAX)) (PreH3 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH4 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH5 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH6 : (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) )) (PreH7 : (point_in_bound pivot0_low_level_spec )) (PreH8 : (points_in_bound l_low_level_spec )) (PreH9 : (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec )) ,
  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (0 <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= 0) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_3 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (PreH1 : (1 <= tail_n_pre)) (PreH2 : (tail_n_pre < INT_MAX)) (PreH3 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH4 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH5 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH6 : (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) )) (PreH7 : (point_in_bound pivot0_low_level_spec )) (PreH8 : (points_in_bound l_low_level_spec )) (PreH9 : (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec )) ,
  ((( &( "top" ) )) # Int  |->_)
  **  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_4 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (PreH1 : (1 <= tail_n_pre)) (PreH2 : (tail_n_pre < INT_MAX)) (PreH3 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH4 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH5 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH6 : (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) )) (PreH7 : (point_in_bound pivot0_low_level_spec )) (PreH8 : (points_in_bound l_low_level_spec )) (PreH9 : (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "top" ) )) # Int  |-> 0)
  **  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_5 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < tail_n_pre)) (PreH3 : (top <= i)) (PreH4 : (0 <= tail_n_pre)) (PreH5 : (tail_n_pre < INT_MAX)) (PreH6 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH7 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH8 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH9 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH10 : (point_in_bound pivot0_low_level_spec )) (PreH11 : (points_in_bound l_low_level_spec )) (PreH12 : (points_in_bound (rev (stk)) )) (PreH13 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_6 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_7 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_8 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_9 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_10 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH2 : (top >= 1)) (PreH3 : (0 <= i)) (PreH4 : (i < tail_n_pre)) (PreH5 : (top <= i)) (PreH6 : (0 <= tail_n_pre)) (PreH7 : (tail_n_pre < INT_MAX)) (PreH8 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH9 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH10 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH11 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH12 : (point_in_bound pivot0_low_level_spec )) (PreH13 : (points_in_bound l_low_level_spec )) (PreH14 : (points_in_bound (rev (stk)) )) (PreH15 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_11 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH3 : (top >= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < tail_n_pre)) (PreH6 : (top <= i)) (PreH7 : (0 <= tail_n_pre)) (PreH8 : (tail_n_pre < INT_MAX)) (PreH9 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH10 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH11 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH12 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH13 : (point_in_bound pivot0_low_level_spec )) (PreH14 : (points_in_bound l_low_level_spec )) (PreH15 : (points_in_bound (rev (stk)) )) (PreH16 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((top - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top - 1 )) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_12 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (PreH1 : (top < 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_13 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH3 : (top >= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < tail_n_pre)) (PreH6 : (top <= i)) (PreH7 : (0 <= tail_n_pre)) (PreH8 : (tail_n_pre < INT_MAX)) (PreH9 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH10 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH11 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH12 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH13 : (point_in_bound pivot0_low_level_spec )) (PreH14 : (points_in_bound l_low_level_spec )) (PreH15 : (points_in_bound (rev (stk)) )) (PreH16 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_14 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top < 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> (top + 1 ))
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_15 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH3 : (top >= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < tail_n_pre)) (PreH6 : (top <= i)) (PreH7 : (0 <= tail_n_pre)) (PreH8 : (tail_n_pre < INT_MAX)) (PreH9 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH10 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH11 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH12 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH13 : (point_in_bound pivot0_low_level_spec )) (PreH14 : (points_in_bound l_low_level_spec )) (PreH15 : (points_in_bound (rev (stk)) )) (PreH16 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> (top + 1 ))
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_16 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (PreH1 : (i >= tail_n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((top + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (top + 1 )) ”
.

Definition build_hull_from_sorted_tail_dedup_safety_wit_17 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (PreH1 : (i >= tail_n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_hull_from_sorted_tail_dedup_entail_wit_1 := 
(
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (PreH1 : (1 <= tail_n_pre)) (PreH2 : (tail_n_pre < INT_MAX)) (PreH3 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH4 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH5 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH6 : (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) )) (PreH7 : (point_in_bound pivot0_low_level_spec )) (PreH8 : (points_in_bound l_low_level_spec )) (PreH9 : (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec )) ,
  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((0 + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) (0)) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (0 + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
) \/
(
forall (hull_pre: Z) (tail_n_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (PreH1 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH2 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH3 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH4 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH5 : (1 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH8 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH9 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH10 : (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec )) ,
  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((0 + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) (0)) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.seg hull_pre 0 (0 + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
).

Definition build_hull_from_sorted_tail_dedup_entail_wit_2 := 
(
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (PreH1 : (i < tail_n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk_2)) )) (PreH14 : (safeExec (equiv (stk_2)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec )) ,
  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
) \/
(
forall (hull_pre: Z) (tail_n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (PreH1 : (i < tail_n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk_2)) )) (PreH14 : (safeExec (equiv (stk_2)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ ((rev (stk_2)) = (rev (stk))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
).

Definition build_hull_from_sorted_tail_dedup_entail_wit_3 := 
(
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH3 : (top >= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < tail_n_pre)) (PreH6 : (top <= i)) (PreH7 : (0 <= tail_n_pre)) (PreH8 : (tail_n_pre < INT_MAX)) (PreH9 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH10 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH11 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH12 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH13 : (point_in_bound pivot0_low_level_spec )) (PreH14 : (points_in_bound l_low_level_spec )) (PreH15 : (points_in_bound (rev (stk_2)) )) (PreH16 : (safeExec (equiv (stk_2)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ ((top - 1 ) <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (((top - 1 ) + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 ((top - 1 ) + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre ((top - 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
) \/
(
forall (hull_pre: Z) (tail_n_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH2 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH3 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH4 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH5 : (retval <= 0)) (PreH6 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH7 : (top >= 1)) (PreH8 : (0 <= i)) (PreH9 : (i < tail_n_pre)) (PreH10 : (top <= i)) (PreH11 : (0 <= tail_n_pre)) (PreH12 : (tail_n_pre < INT_MAX)) (PreH13 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH14 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH15 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH16 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH17 : (point_in_bound pivot0_low_level_spec )) (PreH18 : (points_in_bound l_low_level_spec )) (PreH19 : (points_in_bound (rev (stk_2)) )) (PreH20 : (safeExec (equiv (stk_2)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ ((top - 1 ) <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (((top - 1 ) + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.seg hull_pre 0 ((top - 1 ) + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre ((top - 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
).

Definition build_hull_from_sorted_tail_dedup_entail_wit_4_1 := 
(
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top < 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk_2)) )) (PreH14 : (safeExec (equiv (stk_2)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= tail_n_pre) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (((top + 1 ) + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) ((i + 1 ))) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 ((top + 1 ) + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
) \/
(
forall (hull_pre: Z) (tail_n_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH2 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH3 : ((point_y ((Znth i l_low_level_spec __default_Point))) <= INT_MAX)) (PreH4 : ((point_x ((Znth i l_low_level_spec __default_Point))) <= INT_MAX)) (PreH5 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH6 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH7 : ((point_y ((Znth i l_low_level_spec __default_Point))) >= INT_MIN)) (PreH8 : ((point_x ((Znth i l_low_level_spec __default_Point))) >= INT_MIN)) (PreH9 : (top < 1)) (PreH10 : (0 <= i)) (PreH11 : (i < tail_n_pre)) (PreH12 : (top <= i)) (PreH13 : (0 <= tail_n_pre)) (PreH14 : (tail_n_pre < INT_MAX)) (PreH15 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH16 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH17 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH18 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH19 : (point_in_bound pivot0_low_level_spec )) (PreH20 : (points_in_bound l_low_level_spec )) (PreH21 : (points_in_bound (rev (stk_2)) )) (PreH22 : (safeExec (equiv (stk_2)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= tail_n_pre) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (((top + 1 ) + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) ((i + 1 ))) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.seg hull_pre 0 ((top + 1 ) + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
).

Definition build_hull_from_sorted_tail_dedup_entail_wit_4_2 := 
(
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH3 : (top >= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < tail_n_pre)) (PreH6 : (top <= i)) (PreH7 : (0 <= tail_n_pre)) (PreH8 : (tail_n_pre < INT_MAX)) (PreH9 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH10 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH11 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH12 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH13 : (point_in_bound pivot0_low_level_spec )) (PreH14 : (points_in_bound l_low_level_spec )) (PreH15 : (points_in_bound (rev (stk_2)) )) (PreH16 : (safeExec (equiv (stk_2)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= tail_n_pre) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (((top + 1 ) + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) ((i + 1 ))) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 ((top + 1 ) + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
) \/
(
forall (hull_pre: Z) (tail_n_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH2 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH3 : ((point_y ((Znth i l_low_level_spec __default_Point))) <= INT_MAX)) (PreH4 : ((point_x ((Znth i l_low_level_spec __default_Point))) <= INT_MAX)) (PreH5 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH6 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH7 : ((point_y ((Znth i l_low_level_spec __default_Point))) >= INT_MIN)) (PreH8 : ((point_x ((Znth i l_low_level_spec __default_Point))) >= INT_MIN)) (PreH9 : (retval > 0)) (PreH10 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk_2)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk_2)) )) (PreH24 : (safeExec (equiv (stk_2)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= tail_n_pre) ” 
  &&  “ ((top + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (((top + 1 ) + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_iter (l_low_level_spec) ((i + 1 ))) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.seg hull_pre 0 ((top + 1 ) + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
).

Definition build_hull_from_sorted_tail_dedup_return_wit_1 := 
(
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (PreH1 : (i >= tail_n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk_2)) )) (PreH14 : (safeExec (equiv (stk_2)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec )) ,
  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk_2)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (return (tt)) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
) \/
(
forall (hull_pre: Z) (tail_n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk_2: (@list Point)) (top: Z) (i: Z) (PreH1 : (i >= tail_n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk_2)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk_2)) )) (PreH14 : (safeExec (equiv (stk_2)) (build_hull_c_iter (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  EX (stk: (@list Point)) ,
  “ ((rev (stk_2)) = (rev (stk))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (return (tt)) X_low_level_spec ) ”
  &&  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
).

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (PreH1 : (1 <= tail_n_pre)) (PreH2 : (tail_n_pre < INT_MAX)) (PreH3 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH4 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH5 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH6 : (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) )) (PreH7 : (point_in_bound pivot0_low_level_spec )) (PreH8 : (points_in_bound l_low_level_spec )) (PreH9 : (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec )) ,
  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre 0 (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (1 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre 0 (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_2 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (PreH1 : (1 <= tail_n_pre)) (PreH2 : (tail_n_pre < INT_MAX)) (PreH3 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH4 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH5 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH6 : (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) )) (PreH7 : (point_in_bound pivot0_low_level_spec )) (PreH8 : (points_in_bound l_low_level_spec )) (PreH9 : (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec )) ,
  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre 0 (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (1 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre (0 + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_3 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))))
  **  (PointArray.missing_i hull_pre (top - 1 ) 0 (top + 1 ) (rev (stk)) )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_4 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))))
  **  (PointArray.missing_i hull_pre (top - 1 ) 0 (top + 1 ) (rev (stk)) )
  **  ((&(((hull_pre + ((top - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_5 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (top * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))))
  **  (PointArray.missing_i hull_pre top 0 (top + 1 ) (rev (stk)) )
  **  ((&(((hull_pre + (top * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_6 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (top * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))))
  **  (PointArray.missing_i hull_pre top 0 (top + 1 ) (rev (stk)) )
  **  ((&(((hull_pre + (top * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_7 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_8 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure := 
(
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((point_y ((Znth i l_low_level_spec __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_x ((Znth i l_low_level_spec __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ”
) \/
(
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((-point_bound) <= (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_x ((Znth i l_low_level_spec __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_y ((Znth i l_low_level_spec __default_Point))) <= point_bound) ”
).

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_1 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((-point_bound) <= (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_2 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_3 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((-point_bound) <= (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_4 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_5 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((-point_bound) <= (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_6 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_7 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((-point_bound) <= (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_8 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_9 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((-point_bound) <= (point_x ((Znth i l_low_level_spec __default_Point)))) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_10 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((point_x ((Znth i l_low_level_spec __default_Point))) <= point_bound) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_11 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((-point_bound) <= (point_y ((Znth i l_low_level_spec __default_Point)))) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure_split_goal_12 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top <= INT_MAX)) (PreH2 : (tail_n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : ((point_x (pivot0_low_level_spec)) <= INT_MAX)) (PreH5 : ((point_y (pivot0_low_level_spec)) <= INT_MAX)) (PreH6 : (top >= INT_MIN)) (PreH7 : (tail_n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : ((point_x (pivot0_low_level_spec)) >= INT_MIN)) (PreH10 : ((point_y (pivot0_low_level_spec)) >= INT_MIN)) (PreH11 : (top >= 1)) (PreH12 : (0 <= i)) (PreH13 : (i < tail_n_pre)) (PreH14 : (top <= i)) (PreH15 : (0 <= tail_n_pre)) (PreH16 : (tail_n_pre < INT_MAX)) (PreH17 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH18 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH19 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH20 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH21 : (point_in_bound pivot0_low_level_spec )) (PreH22 : (points_in_bound l_low_level_spec )) (PreH23 : (points_in_bound (rev (stk)) )) (PreH24 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "tail_n" ) )) # Int  |-> tail_n_pre)
  **  ((( &( "top" ) )) # Int  |-> top)
  **  ((( &( "pivot" ) )) # Ptr  |-> pivot_pre)
  **  ((( &( "sorted_tail" ) )) # Ptr  |-> sorted_tail_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((point_y ((Znth i l_low_level_spec __default_Point))) <= point_bound) ”
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9_aux := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top >= 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ ((point_y ((Znth i l_low_level_spec __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_x ((Znth i l_low_level_spec __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i l_low_level_spec __default_Point)))) ” 
  &&  “ ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_9 := build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure -> build_hull_from_sorted_tail_dedup_partial_solve_wit_9_aux.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_10 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top < 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_11 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (PreH1 : (top < 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_12 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH3 : (top >= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < tail_n_pre)) (PreH6 : (top <= i)) (PreH7 : (0 <= tail_n_pre)) (PreH8 : (tail_n_pre < INT_MAX)) (PreH9 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH10 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH11 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH12 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH13 : (point_in_bound pivot0_low_level_spec )) (PreH14 : (points_in_bound l_low_level_spec )) (PreH15 : (points_in_bound (rev (stk)) )) (PreH16 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_13 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH3 : (top >= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < tail_n_pre)) (PreH6 : (top <= i)) (PreH7 : (0 <= tail_n_pre)) (PreH8 : (tail_n_pre < INT_MAX)) (PreH9 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH10 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH11 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH12 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH13 : (point_in_bound pivot0_low_level_spec )) (PreH14 : (points_in_bound l_low_level_spec )) (PreH15 : (points_in_bound (rev (stk)) )) (PreH16 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (top + 1 ) (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_14 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z)  __default_Point (PreH1 : (top < 1)) (PreH2 : (0 <= i)) (PreH3 : (i < tail_n_pre)) (PreH4 : (top <= i)) (PreH5 : (0 <= tail_n_pre)) (PreH6 : (tail_n_pre < INT_MAX)) (PreH7 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH8 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH9 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH10 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH11 : (point_in_bound pivot0_low_level_spec )) (PreH12 : (points_in_bound l_low_level_spec )) (PreH13 : (points_in_bound (rev (stk)) )) (PreH14 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (top < 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

Definition build_hull_from_sorted_tail_dedup_partial_solve_wit_15 := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (n_full_low_level_spec: Z) (l_low_level_spec: (@list Point)) (pivot0_low_level_spec: Point) (stk: (@list Point)) (top: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point))))))) (PreH3 : (top >= 1)) (PreH4 : (0 <= i)) (PreH5 : (i < tail_n_pre)) (PreH6 : (top <= i)) (PreH7 : (0 <= tail_n_pre)) (PreH8 : (tail_n_pre < INT_MAX)) (PreH9 : (tail_n_pre = (Zlength (l_low_level_spec)))) (PreH10 : ((top + 1 ) = (Zlength ((rev (stk)))))) (PreH11 : ((tail_n_pre + 1 ) <= n_full_low_level_spec)) (PreH12 : (point_polar_sorted pivot0_low_level_spec l_low_level_spec )) (PreH13 : (point_in_bound pivot0_low_level_spec )) (PreH14 : (points_in_bound l_low_level_spec )) (PreH15 : (points_in_bound (rev (stk)) )) (PreH16 : (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec )) ,
  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth ((top - 1 ) - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_y ((Znth (top - 0 ) (rev (stk)) __default_Point)))) ((point_x ((Znth i l_low_level_spec __default_Point)))) ((point_y ((Znth i l_low_level_spec __default_Point)))))) ” 
  &&  “ (top >= 1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < tail_n_pre) ” 
  &&  “ (top <= i) ” 
  &&  “ (0 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ ((top + 1 ) = (Zlength ((rev (stk))))) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (build_hull_c_step (l_low_level_spec) (i)) X_low_level_spec ) ”
  &&  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.missing_i sorted_tail_pre i 0 tail_n_pre l_low_level_spec )
  **  ((&(((sorted_tail_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i l_low_level_spec __default_Point))))
  **  (PointArray.undef_seg hull_pre ((top + 1 ) + 1 ) (tail_n_pre + 1 ) )
  **  ((&(((hull_pre + ((top + 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.seg hull_pre 0 (top + 1 ) (rev (stk)) )
  **  ((&((pivot_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0_low_level_spec)))
  **  ((&((pivot_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0_low_level_spec)))
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec )
.

(*----- Function swap_points -----*)

Definition swap_points_return_wit_1 := 
(
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  (PointArray.full pts_pre n_pre (replace_Znth (j_pre) ((point_mk ((point_x ((Znth j_pre (replace_Znth (j_pre) ((point_mk ((point_x ((Znth i_pre pts_l __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))))) __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) ((replace_Znth (j_pre) ((point_mk ((point_x ((Znth i_pre pts_l __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))))))) )
|--
  “ ((Zlength (pts_l)) = n_pre) ”
  &&  (PointArray.full pts_pre n_pre (point_swap (pts_l) (i_pre) (j_pre)) )
) \/
(
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  TT && emp 
|--
  “ ((replace_Znth (j_pre) ((point_mk ((point_x ((Znth j_pre (replace_Znth (j_pre) ((point_mk ((point_x ((Znth i_pre pts_l __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))))) __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) ((replace_Znth (j_pre) ((point_mk ((point_x ((Znth i_pre pts_l __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))))))) = (point_swap (pts_l) (i_pre) (j_pre))) ”
  &&  emp
).

Definition swap_points_return_wit_1_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  ((replace_Znth (j_pre) ((point_mk ((point_x ((Znth j_pre (replace_Znth (j_pre) ((point_mk ((point_x ((Znth i_pre pts_l __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))))) __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) ((replace_Znth (j_pre) ((point_mk ((point_x ((Znth i_pre pts_l __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))))))) = (point_swap (pts_l) (i_pre) (j_pre)))
.

Definition swap_points_partial_solve_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i_pre pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre i_pre 0 n_pre pts_l )
  **  ((&(((pts_pre + (i_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i_pre pts_l __default_Point))))
.

Definition swap_points_partial_solve_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i_pre pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre i_pre 0 n_pre pts_l )
  **  ((&(((pts_pre + (i_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i_pre pts_l __default_Point))))
.

Definition swap_points_partial_solve_wit_3 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (j_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth j_pre pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre j_pre 0 n_pre pts_l )
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth j_pre pts_l __default_Point))))
.

Definition swap_points_partial_solve_wit_4 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.missing_i pts_pre i_pre 0 n_pre pts_l )
  **  ((&(((pts_pre + (i_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i_pre pts_l __default_Point))))
.

Definition swap_points_partial_solve_wit_5 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  (PointArray.full pts_pre n_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (j_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point))))
  **  (PointArray.missing_i pts_pre j_pre 0 n_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) )
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point))))
.

Definition swap_points_partial_solve_wit_6 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  (PointArray.full pts_pre n_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.missing_i pts_pre i_pre 0 n_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) )
  **  ((&(((pts_pre + (i_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point))))
.

Definition swap_points_partial_solve_wit_7 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  (PointArray.full pts_pre n_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (j_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.missing_i pts_pre j_pre 0 n_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) )
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point))))
.

Definition swap_points_partial_solve_wit_8 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : (i_pre <> j_pre)) (PreH6 : ((Zlength (pts_l)) = n_pre)) ,
  (PointArray.full pts_pre n_pre (replace_Znth (j_pre) ((point_mk ((point_x ((Znth i_pre pts_l __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))))) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ (i_pre <> j_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ”
  &&  ((&(((pts_pre + (j_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.missing_i pts_pre j_pre 0 n_pre (replace_Znth (j_pre) ((point_mk ((point_x ((Znth i_pre pts_l __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))))) )
  **  ((&(((pts_pre + (j_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth j_pre (replace_Znth (j_pre) ((point_mk ((point_x ((Znth i_pre pts_l __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth i_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))) ((point_y ((Znth j_pre (replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)) __default_Point)))))) ((replace_Znth (i_pre) ((point_mk ((point_x ((Znth j_pre pts_l __default_Point)))) ((point_y ((Znth i_pre pts_l __default_Point)))))) (pts_l)))))) __default_Point))))
.

(*----- Function partition_polar_points -----*)

Definition partition_polar_points_safety_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  ((( &( "pivot_y" ) )) # Int  |-> (point_y ((Znth high_pre pts_l __default_Point))))
  **  ((( &( "pivot_x" ) )) # Int  |-> (point_x ((Znth high_pre pts_l __default_Point))))
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((low_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low_pre - 1 )) ”
.

Definition partition_polar_points_safety_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  ((( &( "pivot_y" ) )) # Int  |-> (point_y ((Znth high_pre pts_l __default_Point))))
  **  ((( &( "pivot_x" ) )) # Int  |-> (point_x ((Znth high_pre pts_l __default_Point))))
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH2 : (j < high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |-> retval)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition partition_polar_points_safety_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |-> retval)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_5 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (j)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_polar_points_safety_wit_6 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur )) (PreH17 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH22 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_polar_points_safety_wit_7 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_polar_points_safety_wit_8 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j >= high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH18 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH19 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_9 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j >= high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH18 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH19 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_10 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_11 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_12 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_13 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_polar_points_safety_wit_14 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_safety_wit_15 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_polar_points_entail_wit_1 := 
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (low_pre - 1 )) ” 
  &&  “ ((low_pre - 1 ) < low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = (point_x ((Znth high_pre pts_l __default_Point)))) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = (point_y ((Znth high_pre pts_l __default_Point)))) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre ) ” 
  &&  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) (low_pre - 1 ) low_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  TT && emp 
|--
  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_l low_pre high_pre (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) (low_pre - 1 ) low_pre ) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) ) ” 
  &&  “ (((Znth high_pre pts_l __default_Point).(y) ) = (point_y ((Znth high_pre pts_l __default_Point)))) ” 
  &&  “ (((Znth high_pre pts_l __default_Point).(x) ) = (point_x ((Znth high_pre pts_l __default_Point)))) ”
  &&  emp
).

Definition partition_polar_points_entail_wit_1_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_l low_pre high_pre (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) (low_pre - 1 ) low_pre )
.

Definition partition_polar_points_entail_wit_1_split_goal_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  (point_in_bound (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) )
.

Definition partition_polar_points_entail_wit_1_split_goal_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  (((Znth high_pre pts_l __default_Point).(y) ) = (point_y ((Znth high_pre pts_l __default_Point))))
.

Definition partition_polar_points_entail_wit_1_split_goal_4 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  (((Znth high_pre pts_l __default_Point).(x) ) = (point_x ((Znth high_pre pts_l __default_Point))))
.

Definition partition_polar_points_entail_wit_2_1 := 
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre ) ” 
  &&  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l (point_swap (pts_cur_2) ((i + 1 )) (j)) low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur_2) ((i + 1 )) (j)) low_pre high_pre ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur_2) ((i + 1 )) (j)) ) ” 
  &&  “ (points_in_bound (point_swap (pts_cur_2) ((i + 1 )) (j)) ) ” 
  &&  “ (((Znth high_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth high_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) __default_Point).(x) ) = pivot_x) ” 
  &&  “ ((Zlength ((point_swap (pts_cur_2) ((i + 1 )) (j)))) = n_pre) ”
  &&  emp
).

Definition partition_polar_points_entail_wit_2_1_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l (point_swap (pts_cur_2) ((i + 1 )) (j)) low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) )
.

Definition partition_polar_points_entail_wit_2_1_split_goal_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur_2) ((i + 1 )) (j)) low_pre high_pre )
.

Definition partition_polar_points_entail_wit_2_1_split_goal_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (leftmost (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur_2) ((i + 1 )) (j)) )
.

Definition partition_polar_points_entail_wit_2_1_split_goal_4 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (points_in_bound (point_swap (pts_cur_2) ((i + 1 )) (j)) )
.

Definition partition_polar_points_entail_wit_2_1_split_goal_5 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (((Znth high_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) __default_Point).(y) ) = pivot_y)
.

Definition partition_polar_points_entail_wit_2_1_split_goal_6 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (((Znth high_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) __default_Point).(x) ) = pivot_x)
.

Definition partition_polar_points_entail_wit_2_1_split_goal_7 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH19 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH23 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((Zlength ((point_swap (pts_cur_2) ((i + 1 )) (j)))) = n_pre)
.

Definition partition_polar_points_entail_wit_2_2 := 
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH22 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre ) ” 
  &&  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH22 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  emp
).

Definition partition_polar_points_entail_wit_2_2_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH22 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) )
.

Definition partition_polar_points_entail_wit_2_3 := 
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur_2)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
|--
  EX (pts_cur: (@list Point)) ,
  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre ) ” 
  &&  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i (j + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur_2)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i (j + 1 ) ) ”
  &&  emp
).

Definition partition_polar_points_entail_wit_2_3_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur_2)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur_2 )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur_2 low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i (j + 1 ) )
.

Definition partition_polar_points_return_wit_1 := 
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
|--
  EX (pts_out: (@list Point)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out low_pre high_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out low_pre high_pre ) ” 
  &&  “ (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out low_pre high_pre (i + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre (i + 1 ) ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre ) ” 
  &&  “ (point_same_outside_range pts_l (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre ) ” 
  &&  “ (point_permutation pts_l (point_swap (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (points_in_bound (point_swap (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ ((Zlength ((point_swap (pts_cur) ((i + 1 )) (high_pre)))) = n_pre) ”
  &&  emp
).

Definition partition_polar_points_return_wit_1_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre (i + 1 ) )
.

Definition partition_polar_points_return_wit_1_split_goal_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre )
.

Definition partition_polar_points_return_wit_1_split_goal_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_same_outside_range pts_l (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre )
.

Definition partition_polar_points_return_wit_1_split_goal_4 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_permutation pts_l (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
.

Definition partition_polar_points_return_wit_1_split_goal_5 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (leftmost (point_mk (gx_pre) (gy_pre)) (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
.

Definition partition_polar_points_return_wit_1_split_goal_6 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (points_in_bound (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
.

Definition partition_polar_points_return_wit_1_split_goal_7 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH20 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH21 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((Zlength ((point_swap (pts_cur) ((i + 1 )) (high_pre)))) = n_pre)
.

Definition partition_polar_points_return_wit_2 := 
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
|--
  EX (pts_out: (@list Point)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out low_pre high_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out low_pre high_pre ) ” 
  &&  “ (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out low_pre high_pre (i + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre (i + 1 ) ) ” 
  &&  “ (point_same_outside_range pts_l pts_cur low_pre high_pre ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ”
  &&  emp
).

Definition partition_polar_points_return_wit_2_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre (i + 1 ) )
.

Definition partition_polar_points_return_wit_2_split_goal_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_same_outside_range pts_l pts_cur low_pre high_pre )
.

Definition partition_polar_points_return_wit_2_split_goal_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_permutation pts_l pts_cur )
.

Definition partition_polar_points_partial_solve_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre ) ”
  &&  ((&(((pts_pre + (high_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth high_pre pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre high_pre 0 n_pre pts_l )
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth high_pre pts_l __default_Point))))
.

Definition partition_polar_points_partial_solve_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) (PreH8 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH9 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre )) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l low_pre high_pre ) ”
  &&  ((&(((pts_pre + (high_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth high_pre pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre high_pre 0 n_pre pts_l )
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth high_pre pts_l __default_Point))))
.

Definition partition_polar_points_partial_solve_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j < high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH18 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH19 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (j < high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre ) ” 
  &&  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts_pre + (j * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre j 0 n_pre pts_cur )
  **  ((&(((pts_pre + (j * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
.

Definition partition_polar_points_partial_solve_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j < high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH18 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH19 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (j < high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre ) ” 
  &&  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts_pre + (j * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre j 0 n_pre pts_cur )
  **  ((&(((pts_pre + (j * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
.

Definition partition_polar_points_partial_solve_wit_5_pure := 
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j < high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH18 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH19 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_polar_cmp_safe_pair (point_mk (gx_pre) (gy_pre)) (point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point))))) (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point))))) ) ”
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (pivot_y <= INT_MAX)) (PreH2 : (pivot_x <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((point_x ((Znth j pts_cur __default_Point))) <= INT_MAX)) (PreH11 : ((point_y ((Znth j pts_cur __default_Point))) <= INT_MAX)) (PreH12 : (pivot_y >= INT_MIN)) (PreH13 : (pivot_x >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((point_x ((Znth j pts_cur __default_Point))) >= INT_MIN)) (PreH22 : ((point_y ((Znth j pts_cur __default_Point))) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((Zlength (pts_cur)) = n_pre)) (PreH25 : (0 <= n_pre)) (PreH26 : (n_pre <= 50000)) (PreH27 : (0 <= low_pre)) (PreH28 : (low_pre <= high_pre)) (PreH29 : (high_pre < n_pre)) (PreH30 : ((low_pre - 1 ) <= i)) (PreH31 : (i < j)) (PreH32 : (j <= high_pre)) (PreH33 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH34 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH35 : (points_in_bound pts_cur )) (PreH36 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH37 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH38 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH39 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH40 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH41 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ (point_in_bound (point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point))))) ) ” 
  &&  “ (point_polar_cmp_safe_pair (point_mk (gx_pre) (gy_pre)) (point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point))))) (point_mk (pivot_x) (pivot_y)) ) ”
).

Definition partition_polar_points_partial_solve_wit_5_pure_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (pivot_y <= INT_MAX)) (PreH2 : (pivot_x <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((point_x ((Znth j pts_cur __default_Point))) <= INT_MAX)) (PreH11 : ((point_y ((Znth j pts_cur __default_Point))) <= INT_MAX)) (PreH12 : (pivot_y >= INT_MIN)) (PreH13 : (pivot_x >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((point_x ((Znth j pts_cur __default_Point))) >= INT_MIN)) (PreH22 : ((point_y ((Znth j pts_cur __default_Point))) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((Zlength (pts_cur)) = n_pre)) (PreH25 : (0 <= n_pre)) (PreH26 : (n_pre <= 50000)) (PreH27 : (0 <= low_pre)) (PreH28 : (low_pre <= high_pre)) (PreH29 : (high_pre < n_pre)) (PreH30 : ((low_pre - 1 ) <= i)) (PreH31 : (i < j)) (PreH32 : (j <= high_pre)) (PreH33 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH34 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH35 : (points_in_bound pts_cur )) (PreH36 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH37 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH38 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH39 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH40 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH41 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ (point_in_bound (point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point))))) ) ”
.

Definition partition_polar_points_partial_solve_wit_5_pure_split_goal_2 := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (pivot_y <= INT_MAX)) (PreH2 : (pivot_x <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((point_x ((Znth j pts_cur __default_Point))) <= INT_MAX)) (PreH11 : ((point_y ((Znth j pts_cur __default_Point))) <= INT_MAX)) (PreH12 : (pivot_y >= INT_MIN)) (PreH13 : (pivot_x >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((point_x ((Znth j pts_cur __default_Point))) >= INT_MIN)) (PreH22 : ((point_y ((Znth j pts_cur __default_Point))) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((Zlength (pts_cur)) = n_pre)) (PreH25 : (0 <= n_pre)) (PreH26 : (n_pre <= 50000)) (PreH27 : (0 <= low_pre)) (PreH28 : (low_pre <= high_pre)) (PreH29 : (high_pre < n_pre)) (PreH30 : ((low_pre - 1 ) <= i)) (PreH31 : (i < j)) (PreH32 : (j <= high_pre)) (PreH33 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH34 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH35 : (points_in_bound pts_cur )) (PreH36 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH37 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH38 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH39 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH40 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH41 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ (point_polar_cmp_safe_pair (point_mk (gx_pre) (gy_pre)) (point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point))))) (point_mk (pivot_x) (pivot_y)) ) ”
.

Definition partition_polar_points_partial_solve_wit_5_aux := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j < high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH18 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH19 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_polar_cmp_safe_pair (point_mk (gx_pre) (gy_pre)) (point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point))))) (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point))))) ) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre ) ” 
  &&  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_partial_solve_wit_5 := partition_polar_points_partial_solve_wit_5_pure -> partition_polar_points_partial_solve_wit_5_aux.

Definition partition_polar_points_partial_solve_wit_6_pure := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur )) (PreH17 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH22 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |-> retval)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ”
.

Definition partition_polar_points_partial_solve_wit_6_aux := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur )) (PreH17 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH22 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (point_cmp_polar ((point_mk (gx_pre) (gy_pre))) ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y))))) ” 
  &&  “ (j < high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre ) ” 
  &&  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_partial_solve_wit_6 := partition_polar_points_partial_solve_wit_6_pure -> partition_polar_points_partial_solve_wit_6_aux.

Definition partition_polar_points_partial_solve_wit_7_pure := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ”
.

Definition partition_polar_points_partial_solve_wit_7_aux := 
forall (gy_pre: Z) (gx_pre: Z) (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre )) (PreH20 : (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x) ” 
  &&  “ (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_cur ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_cur low_pre high_pre ) ” 
  &&  “ (point_polar_partition_scan_inv (point_mk (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_polar_points_partial_solve_wit_7 := partition_polar_points_partial_solve_wit_7_pure -> partition_polar_points_partial_solve_wit_7_aux.

(*----- Function quicksort_polar_points -----*)

Definition quicksort_polar_points_safety_wit_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : ((Zlength (pts_out)) = n_pre)) (PreH5 : (points_in_bound pts_out )) (PreH6 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH7 : (point_permutation pts_l pts_out )) (PreH8 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH9 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH10 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (pts_l)) = n_pre)) (PreH18 : (points_in_bound pts_l )) (PreH19 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quicksort_polar_points_safety_wit_2 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : ((Zlength (pts_out)) = n_pre)) (PreH5 : (points_in_bound pts_out )) (PreH6 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH7 : (point_permutation pts_l pts_out )) (PreH8 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH9 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH10 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (pts_l)) = n_pre)) (PreH18 : (points_in_bound pts_l )) (PreH19 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_polar_points_safety_wit_3 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH8 : (point_permutation pts_l pts_out )) (PreH9 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH11 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : ((-1) <= right_pre)) (PreH17 : (right_pre < n_pre)) (PreH18 : ((Zlength (pts_l)) = n_pre)) (PreH19 : (points_in_bound pts_l )) (PreH20 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ False ”
.

Definition quicksort_polar_points_safety_wit_4 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (pts_out_2: (@list Point)) (PreH1 : (retval < right_pre)) (PreH2 : ((Zlength (pts_out_2)) = n_pre)) (PreH3 : (points_in_bound pts_out_2 )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH5 : (point_permutation pts_out pts_out_2 )) (PreH6 : (point_same_outside_range pts_out pts_out_2 left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out)) = n_pre)) (PreH13 : (points_in_bound pts_out )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH15 : (point_permutation pts_l pts_out )) (PreH16 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_polar_points_safety_wit_5 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (pts_out_2: (@list Point)) (PreH1 : (retval < right_pre)) (PreH2 : ((Zlength (pts_out_2)) = n_pre)) (PreH3 : (points_in_bound pts_out_2 )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH5 : (point_permutation pts_out pts_out_2 )) (PreH6 : (point_same_outside_range pts_out pts_out_2 left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out)) = n_pre)) (PreH13 : (points_in_bound pts_out )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH15 : (point_permutation pts_l pts_out )) (PreH16 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_polar_points_safety_wit_6 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH8 : (point_permutation pts_l pts_out )) (PreH9 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH11 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : ((-1) <= right_pre)) (PreH17 : (right_pre < n_pre)) (PreH18 : ((Zlength (pts_l)) = n_pre)) (PreH19 : (points_in_bound pts_l )) (PreH20 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_polar_points_safety_wit_7 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH8 : (point_permutation pts_l pts_out )) (PreH9 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH11 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : ((-1) <= right_pre)) (PreH17 : (right_pre < n_pre)) (PreH18 : ((Zlength (pts_l)) = n_pre)) (PreH19 : (points_in_bound pts_l )) (PreH20 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_polar_points_return_wit_1 := 
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_4 )) (PreH4 : (point_permutation pts_out_3 pts_out_4 )) (PreH5 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : ((Zlength (pts_out_3)) = n_pre)) (PreH10 : (points_in_bound pts_out_3 )) (PreH11 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH12 : (point_permutation pts_out_2 pts_out_3 )) (PreH13 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH14 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH15 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : ((Zlength (pts_out_2)) = n_pre)) (PreH20 : (points_in_bound pts_out_2 )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH22 : (point_permutation pts_l pts_out_2 )) (PreH23 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH24 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH25 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH26 : (left_pre < right_pre)) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : (0 <= left_pre)) (PreH30 : ((-1) <= right_pre)) (PreH31 : (right_pre < n_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : (points_in_bound pts_l )) (PreH34 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH35 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH36 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out_4 )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ” 
  &&  “ (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_4 )) (PreH4 : (point_permutation pts_out_3 pts_out_4 )) (PreH5 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : ((Zlength (pts_out_3)) = n_pre)) (PreH10 : (points_in_bound pts_out_3 )) (PreH11 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH12 : (point_permutation pts_out_2 pts_out_3 )) (PreH13 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH14 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH15 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : ((Zlength (pts_out_2)) = n_pre)) (PreH20 : (points_in_bound pts_out_2 )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH22 : (point_permutation pts_l pts_out_2 )) (PreH23 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH24 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH25 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH26 : (left_pre < right_pre)) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : (0 <= left_pre)) (PreH30 : ((-1) <= right_pre)) (PreH31 : (right_pre < n_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : (points_in_bound pts_l )) (PreH34 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH35 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH36 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  TT && emp 
|--
  “ (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_4 left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_4 left_pre right_pre ) ” 
  &&  “ (point_same_outside_range pts_l pts_out_4 left_pre right_pre ) ” 
  &&  “ (point_permutation pts_l pts_out_4 ) ”
  &&  emp
).

Definition quicksort_polar_points_return_wit_1_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_4 )) (PreH4 : (point_permutation pts_out_3 pts_out_4 )) (PreH5 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : ((Zlength (pts_out_3)) = n_pre)) (PreH10 : (points_in_bound pts_out_3 )) (PreH11 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH12 : (point_permutation pts_out_2 pts_out_3 )) (PreH13 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH14 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH15 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : ((Zlength (pts_out_2)) = n_pre)) (PreH20 : (points_in_bound pts_out_2 )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH22 : (point_permutation pts_l pts_out_2 )) (PreH23 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH24 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH25 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH26 : (left_pre < right_pre)) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : (0 <= left_pre)) (PreH30 : ((-1) <= right_pre)) (PreH31 : (right_pre < n_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : (points_in_bound pts_l )) (PreH34 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH35 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH36 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_4 left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_1_split_goal_2 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_4 )) (PreH4 : (point_permutation pts_out_3 pts_out_4 )) (PreH5 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : ((Zlength (pts_out_3)) = n_pre)) (PreH10 : (points_in_bound pts_out_3 )) (PreH11 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH12 : (point_permutation pts_out_2 pts_out_3 )) (PreH13 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH14 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH15 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : ((Zlength (pts_out_2)) = n_pre)) (PreH20 : (points_in_bound pts_out_2 )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH22 : (point_permutation pts_l pts_out_2 )) (PreH23 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH24 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH25 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH26 : (left_pre < right_pre)) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : (0 <= left_pre)) (PreH30 : ((-1) <= right_pre)) (PreH31 : (right_pre < n_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : (points_in_bound pts_l )) (PreH34 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH35 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH36 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_4 left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_1_split_goal_3 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_4 )) (PreH4 : (point_permutation pts_out_3 pts_out_4 )) (PreH5 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : ((Zlength (pts_out_3)) = n_pre)) (PreH10 : (points_in_bound pts_out_3 )) (PreH11 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH12 : (point_permutation pts_out_2 pts_out_3 )) (PreH13 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH14 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH15 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : ((Zlength (pts_out_2)) = n_pre)) (PreH20 : (points_in_bound pts_out_2 )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH22 : (point_permutation pts_l pts_out_2 )) (PreH23 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH24 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH25 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH26 : (left_pre < right_pre)) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : (0 <= left_pre)) (PreH30 : ((-1) <= right_pre)) (PreH31 : (right_pre < n_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : (points_in_bound pts_l )) (PreH34 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH35 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH36 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_same_outside_range pts_l pts_out_4 left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_1_split_goal_4 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_4 )) (PreH4 : (point_permutation pts_out_3 pts_out_4 )) (PreH5 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_4 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : ((Zlength (pts_out_3)) = n_pre)) (PreH10 : (points_in_bound pts_out_3 )) (PreH11 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH12 : (point_permutation pts_out_2 pts_out_3 )) (PreH13 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH14 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH15 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : ((Zlength (pts_out_2)) = n_pre)) (PreH20 : (points_in_bound pts_out_2 )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH22 : (point_permutation pts_l pts_out_2 )) (PreH23 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH24 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH25 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH26 : (left_pre < right_pre)) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : (0 <= left_pre)) (PreH30 : ((-1) <= right_pre)) (PreH31 : (right_pre < n_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : (points_in_bound pts_l )) (PreH34 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH35 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH36 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_permutation pts_l pts_out_4 )
.

Definition quicksort_polar_points_return_wit_2 := 
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : (retval <= left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out_3 )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ” 
  &&  “ (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : (retval <= left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  TT && emp 
|--
  “ (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_same_outside_range pts_l pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_permutation pts_l pts_out_3 ) ”
  &&  emp
).

Definition quicksort_polar_points_return_wit_2_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : (retval <= left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_2_split_goal_2 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : (retval <= left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_2_split_goal_3 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : (retval <= left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_same_outside_range pts_l pts_out_3 left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_2_split_goal_4 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH7 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 (retval + 1 ) right_pre )) (PreH8 : (retval < right_pre)) (PreH9 : (retval <= left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_permutation pts_l pts_out_3 )
.

Definition quicksort_polar_points_return_wit_3 := 
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH5 : (point_permutation pts_out_2 pts_out_3 )) (PreH6 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out_3 )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ” 
  &&  “ (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH5 : (point_permutation pts_out_2 pts_out_3 )) (PreH6 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  TT && emp 
|--
  “ (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_same_outside_range pts_l pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_permutation pts_l pts_out_3 ) ”
  &&  emp
).

Definition quicksort_polar_points_return_wit_3_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH5 : (point_permutation pts_out_2 pts_out_3 )) (PreH6 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_3_split_goal_2 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH5 : (point_permutation pts_out_2 pts_out_3 )) (PreH6 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_3_split_goal_3 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH5 : (point_permutation pts_out_2 pts_out_3 )) (PreH6 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_same_outside_range pts_l pts_out_3 left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_3_split_goal_4 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_3 )) (PreH5 : (point_permutation pts_out_2 pts_out_3 )) (PreH6 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_permutation pts_l pts_out_3 )
.

Definition quicksort_polar_points_return_wit_4 := 
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) (PreH9 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH10 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH11 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ” 
  &&  “ (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) (PreH9 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH10 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH11 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  TT && emp 
|--
  “ (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre ) ” 
  &&  “ (point_same_outside_range pts_l pts_l left_pre right_pre ) ” 
  &&  “ (point_permutation pts_l pts_l ) ”
  &&  emp
).

Definition quicksort_polar_points_return_wit_4_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) (PreH9 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH10 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH11 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_4_split_goal_2 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) (PreH9 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH10 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH11 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_same_outside_range pts_l pts_l left_pre right_pre )
.

Definition quicksort_polar_points_return_wit_4_split_goal_3 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) (PreH9 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH10 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH11 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (point_permutation pts_l pts_l )
.

Definition quicksort_polar_points_partial_solve_wit_1_pure := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) (PreH9 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH10 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH11 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre ) ”
.

Definition quicksort_polar_points_partial_solve_wit_1_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) (PreH9 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH10 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH11 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
.

Definition quicksort_polar_points_partial_solve_wit_1 := quicksort_polar_points_partial_solve_wit_1_pure -> quicksort_polar_points_partial_solve_wit_1_aux.

Definition quicksort_polar_points_partial_solve_wit_2_pure := 
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : ((Zlength (pts_out)) = n_pre)) (PreH5 : (points_in_bound pts_out )) (PreH6 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH7 : (point_permutation pts_l pts_out )) (PreH8 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH9 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH10 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (pts_l)) = n_pre)) (PreH18 : (points_in_bound pts_l )) (PreH19 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) ) ”
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (gx_pre <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (gx_pre >= INT_MIN)) (PreH11 : (gy_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : ((Zlength (pts_out)) = n_pre)) (PreH17 : (points_in_bound pts_out )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH19 : (point_permutation pts_l pts_out )) (PreH20 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH22 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH23 : (left_pre < right_pre)) (PreH24 : (0 <= n_pre)) (PreH25 : (n_pre <= 50000)) (PreH26 : (0 <= left_pre)) (PreH27 : ((-1) <= right_pre)) (PreH28 : (right_pre < n_pre)) (PreH29 : ((Zlength (pts_l)) = n_pre)) (PreH30 : (points_in_bound pts_l )) (PreH31 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH32 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH33 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) ) ”
).

Definition quicksort_polar_points_partial_solve_wit_2_pure_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (gx_pre <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (gx_pre >= INT_MIN)) (PreH11 : (gy_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : ((Zlength (pts_out)) = n_pre)) (PreH17 : (points_in_bound pts_out )) (PreH18 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH19 : (point_permutation pts_l pts_out )) (PreH20 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH22 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH23 : (left_pre < right_pre)) (PreH24 : (0 <= n_pre)) (PreH25 : (n_pre <= 50000)) (PreH26 : (0 <= left_pre)) (PreH27 : ((-1) <= right_pre)) (PreH28 : (right_pre < n_pre)) (PreH29 : ((Zlength (pts_l)) = n_pre)) (PreH30 : (points_in_bound pts_l )) (PreH31 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH32 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH33 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) ) ”
.

Definition quicksort_polar_points_partial_solve_wit_2_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : ((Zlength (pts_out)) = n_pre)) (PreH5 : (points_in_bound pts_out )) (PreH6 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH7 : (point_permutation pts_l pts_out )) (PreH8 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH9 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH10 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (pts_l)) = n_pre)) (PreH18 : (points_in_bound pts_l )) (PreH19 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH20 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH21 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ” 
  &&  “ (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_partial_solve_wit_2 := quicksort_polar_points_partial_solve_wit_2_pure -> quicksort_polar_points_partial_solve_wit_2_aux.

Definition quicksort_polar_points_partial_solve_wit_3_pure := 
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out: (@list Point)) (PreH1 : (retval < right_pre)) (PreH2 : ((Zlength (pts_out)) = n_pre)) (PreH3 : (points_in_bound pts_out )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH5 : (point_permutation pts_out_2 pts_out )) (PreH6 : (point_same_outside_range pts_out_2 pts_out left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out (retval + 1 ) right_pre ) ”
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out: (@list Point)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (gx_pre <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (gx_pre >= INT_MIN)) (PreH11 : (gy_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : ((Zlength (pts_out)) = n_pre)) (PreH15 : (points_in_bound pts_out )) (PreH16 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH17 : (point_permutation pts_out_2 pts_out )) (PreH18 : (point_same_outside_range pts_out_2 pts_out left_pre (retval - 1 ) )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) )) (PreH20 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) )) (PreH21 : (retval > left_pre)) (PreH22 : (left_pre <= retval)) (PreH23 : (retval <= right_pre)) (PreH24 : ((Zlength (pts_out_2)) = n_pre)) (PreH25 : (points_in_bound pts_out_2 )) (PreH26 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH27 : (point_permutation pts_l pts_out_2 )) (PreH28 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH30 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH31 : (left_pre < right_pre)) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 50000)) (PreH34 : (0 <= left_pre)) (PreH35 : ((-1) <= right_pre)) (PreH36 : (right_pre < n_pre)) (PreH37 : ((Zlength (pts_l)) = n_pre)) (PreH38 : (points_in_bound pts_l )) (PreH39 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH40 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH41 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out (retval + 1 ) right_pre ) ”
).

Definition quicksort_polar_points_partial_solve_wit_3_pure_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out: (@list Point)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (gx_pre <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (gx_pre >= INT_MIN)) (PreH11 : (gy_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : ((Zlength (pts_out)) = n_pre)) (PreH15 : (points_in_bound pts_out )) (PreH16 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH17 : (point_permutation pts_out_2 pts_out )) (PreH18 : (point_same_outside_range pts_out_2 pts_out left_pre (retval - 1 ) )) (PreH19 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) )) (PreH20 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) )) (PreH21 : (retval > left_pre)) (PreH22 : (left_pre <= retval)) (PreH23 : (retval <= right_pre)) (PreH24 : ((Zlength (pts_out_2)) = n_pre)) (PreH25 : (points_in_bound pts_out_2 )) (PreH26 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH27 : (point_permutation pts_l pts_out_2 )) (PreH28 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH30 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH31 : (left_pre < right_pre)) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 50000)) (PreH34 : (0 <= left_pre)) (PreH35 : ((-1) <= right_pre)) (PreH36 : (right_pre < n_pre)) (PreH37 : ((Zlength (pts_l)) = n_pre)) (PreH38 : (points_in_bound pts_l )) (PreH39 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH40 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH41 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out (retval + 1 ) right_pre ) ”
.

Definition quicksort_polar_points_partial_solve_wit_3_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out: (@list Point)) (PreH1 : (retval < right_pre)) (PreH2 : ((Zlength (pts_out)) = n_pre)) (PreH3 : (points_in_bound pts_out )) (PreH4 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH5 : (point_permutation pts_out_2 pts_out )) (PreH6 : (point_same_outside_range pts_out_2 pts_out left_pre (retval - 1 ) )) (PreH7 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) )) (PreH8 : (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : ((Zlength (pts_out_2)) = n_pre)) (PreH13 : (points_in_bound pts_out_2 )) (PreH14 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 )) (PreH15 : (point_permutation pts_l pts_out_2 )) (PreH16 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH17 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre )) (PreH18 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (pts_l)) = n_pre)) (PreH26 : (points_in_bound pts_l )) (PreH27 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH28 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH29 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out (retval + 1 ) right_pre ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_permutation pts_out_2 pts_out ) ” 
  &&  “ (point_same_outside_range pts_out_2 pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (point_sorted_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (points_in_bound pts_out_2 ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out_2 ) ” 
  &&  “ (point_permutation pts_l pts_out_2 ) ” 
  &&  “ (point_same_outside_range pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre ) ” 
  &&  “ (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_partial_solve_wit_3 := quicksort_polar_points_partial_solve_wit_3_pure -> quicksort_polar_points_partial_solve_wit_3_aux.

Definition quicksort_polar_points_partial_solve_wit_4_pure := 
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH8 : (point_permutation pts_l pts_out )) (PreH9 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH11 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : ((-1) <= right_pre)) (PreH17 : (right_pre < n_pre)) (PreH18 : ((Zlength (pts_l)) = n_pre)) (PreH19 : (points_in_bound pts_l )) (PreH20 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out (retval + 1 ) right_pre ) ”
) \/
(
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (gx_pre <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (gx_pre >= INT_MIN)) (PreH11 : (gy_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (retval <= left_pre)) (PreH15 : (left_pre <= retval)) (PreH16 : (retval <= right_pre)) (PreH17 : ((Zlength (pts_out)) = n_pre)) (PreH18 : (points_in_bound pts_out )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH20 : (point_permutation pts_l pts_out )) (PreH21 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH23 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH24 : (left_pre < right_pre)) (PreH25 : (0 <= n_pre)) (PreH26 : (n_pre <= 50000)) (PreH27 : (0 <= left_pre)) (PreH28 : ((-1) <= right_pre)) (PreH29 : (right_pre < n_pre)) (PreH30 : ((Zlength (pts_l)) = n_pre)) (PreH31 : (points_in_bound pts_l )) (PreH32 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH33 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH34 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out (retval + 1 ) right_pre ) ”
).

Definition quicksort_polar_points_partial_solve_wit_4_pure_split_goal_1 := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (gx_pre <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (left_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (gx_pre >= INT_MIN)) (PreH11 : (gy_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (retval <= left_pre)) (PreH15 : (left_pre <= retval)) (PreH16 : (retval <= right_pre)) (PreH17 : ((Zlength (pts_out)) = n_pre)) (PreH18 : (points_in_bound pts_out )) (PreH19 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH20 : (point_permutation pts_l pts_out )) (PreH21 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH23 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH24 : (left_pre < right_pre)) (PreH25 : (0 <= n_pre)) (PreH26 : (n_pre <= 50000)) (PreH27 : (0 <= left_pre)) (PreH28 : ((-1) <= right_pre)) (PreH29 : (right_pre < n_pre)) (PreH30 : ((Zlength (pts_l)) = n_pre)) (PreH31 : (points_in_bound pts_l )) (PreH32 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH33 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH34 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "gy" ) )) # Int  |-> gy_pre)
  **  ((( &( "gx" ) )) # Int  |-> gx_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out (retval + 1 ) right_pre ) ”
.

Definition quicksort_polar_points_partial_solve_wit_4_aux := 
forall (gy_pre: Z) (gx_pre: Z) (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_out )) (PreH8 : (point_permutation pts_l pts_out )) (PreH9 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH10 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre )) (PreH11 : (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : ((-1) <= right_pre)) (PreH17 : (right_pre < n_pre)) (PreH18 : ((Zlength (pts_l)) = n_pre)) (PreH19 : (points_in_bound pts_l )) (PreH20 : (point_in_bound (point_mk (gx_pre) (gy_pre)) )) (PreH21 : (leftmost (point_mk (gx_pre) (gy_pre)) pts_l )) (PreH22 : (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre )) ,
  (PointArray.full pts_pre n_pre pts_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out (retval + 1 ) right_pre ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre ) ” 
  &&  “ (point_polar_partitioned_at (point_mk (gx_pre) (gy_pre)) pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (point_in_bound (point_mk (gx_pre) (gy_pre)) ) ” 
  &&  “ (leftmost (point_mk (gx_pre) (gy_pre)) pts_l ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx_pre) (gy_pre)) pts_l left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_polar_points_partial_solve_wit_4 := quicksort_polar_points_partial_solve_wit_4_pure -> quicksort_polar_points_partial_solve_wit_4_aux.

(*----- Function dedup_points_and_find_leftmost -----*)

Definition dedup_points_and_find_leftmost_safety_wit_1 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pivot0: Z) (pts_l: (@list Point)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (0 <= pivot0)) (PreH5 : (pivot0 < n_pre)) (PreH6 : (points_in_bound pts_l )) ,
  ((( &( "unique_n" ) )) # Int  |->_)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  ((pivot_idx_pre) # Int  |-> pivot0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_2 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pivot0: Z) (pts_l: (@list Point)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (0 <= pivot0)) (PreH5 : (pivot0 < n_pre)) (PreH6 : (points_in_bound pts_l )) ,
  ((( &( "read" ) )) # Int  |->_)
  **  ((( &( "unique_n" ) )) # Int  |-> 0)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  ((pivot_idx_pre) # Int  |-> pivot0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_3 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_cur: Z) (unique_n: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (read < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) ,
  ((( &( "duplicate" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_4 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_cur: Z) (unique_n: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (read < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) ,
  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "duplicate" ) )) # Int  |-> 0)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_5 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((point_y ((Znth scan pts_cur __default_Point))) = (point_y ((Znth read pts_cur __default_Point))))) (PreH2 : ((point_x ((Znth scan pts_cur __default_Point))) = (point_x ((Znth read pts_cur __default_Point))))) (PreH3 : (scan < unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur)) (PreH15 : (pivot_cur < n_pre)) (PreH16 : (points_in_bound pts_cur )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH18 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate)
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_6 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((point_x ((Znth scan pts_cur __default_Point))) <> (point_x ((Znth read pts_cur __default_Point))))) (PreH2 : (scan < unique_n)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= scan)) (PreH10 : (scan <= unique_n)) (PreH11 : (0 <= unique_n)) (PreH12 : (unique_n <= read)) (PreH13 : (0 <= pivot_cur)) (PreH14 : (pivot_cur < n_pre)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH17 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate)
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ ((scan + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_7 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((point_y ((Znth scan pts_cur __default_Point))) <> (point_y ((Znth read pts_cur __default_Point))))) (PreH2 : ((point_x ((Znth scan pts_cur __default_Point))) = (point_x ((Znth read pts_cur __default_Point))))) (PreH3 : (scan < unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur)) (PreH15 : (pivot_cur < n_pre)) (PreH16 : (points_in_bound pts_cur )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH18 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate)
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ ((scan + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_8 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (duplicate_addr_v: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= read)) (PreH6 : (read < n_pre)) (PreH7 : (0 <= unique_n)) (PreH8 : (unique_n <= read)) (PreH9 : (0 <= pivot_cur)) (PreH10 : (pivot_cur < n_pre)) (PreH11 : (points_in_bound pts_cur )) (PreH12 : (point_permutation pts_l pts_cur )) (PreH13 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH14 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH15 : (unique_n = 0)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate_addr_v)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_9 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (duplicate_addr_v: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= read)) (PreH6 : (read < n_pre)) (PreH7 : (0 <= unique_n)) (PreH8 : (unique_n <= read)) (PreH9 : (0 <= pivot_cur)) (PreH10 : (pivot_cur < n_pre)) (PreH11 : (points_in_bound pts_cur )) (PreH12 : (point_permutation pts_l pts_cur )) (PreH13 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH14 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH15 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate_addr_v)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_10 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (duplicate_addr_v: Z) (PreH1 : (unique_n <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (unique_n = 0)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate_addr_v)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ False ”
.

Definition dedup_points_and_find_leftmost_safety_wit_11 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (duplicate_addr_v: Z) (retval: Z)  __default_Point (PreH1 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur __default_Point)))) ((point_y ((Znth unique_n pts_cur __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur pts_cur __default_Point)))) ((point_y ((Znth pivot_cur pts_cur __default_Point))))))))) (PreH2 : (unique_n <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= unique_n)) (PreH10 : (unique_n <= read)) (PreH11 : (0 <= pivot_cur)) (PreH12 : (pivot_cur < n_pre)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_permutation pts_l pts_cur )) (PreH15 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH16 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH17 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate_addr_v)
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_12 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (duplicate_addr_v: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate_addr_v)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> unique_n)
|--
  “ ((unique_n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (unique_n + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_13 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (duplicate_addr_v: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (unique_n = 0)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate_addr_v)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> unique_n)
|--
  “ ((unique_n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (unique_n + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_14 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (duplicate_addr_v: Z) (retval: Z)  __default_Point (PreH1 : (retval < 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur __default_Point)))) ((point_y ((Znth unique_n pts_cur __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur pts_cur __default_Point)))) ((point_y ((Znth pivot_cur pts_cur __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur)) (PreH13 : (pivot_cur < n_pre)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_permutation pts_l pts_cur )) (PreH16 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate_addr_v)
  **  ((pivot_idx_pre) # Int  |-> unique_n)
|--
  “ ((unique_n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (unique_n + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_15 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (duplicate_addr_v: Z) (retval: Z)  __default_Point (PreH1 : (retval >= 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur __default_Point)))) ((point_y ((Znth unique_n pts_cur __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur pts_cur __default_Point)))) ((point_y ((Znth pivot_cur pts_cur __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur)) (PreH13 : (pivot_cur < n_pre)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_permutation pts_l pts_cur )) (PreH16 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate_addr_v)
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ ((unique_n + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (unique_n + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_16 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> (unique_n + 1 ))
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> unique_n)
|--
  “ ((read + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (read + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_17 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (unique_n = 0)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> (unique_n + 1 ))
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> unique_n)
|--
  “ ((read + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (read + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_18 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (retval: Z)  __default_Point (PreH1 : (retval < 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur __default_Point)))) ((point_y ((Znth unique_n pts_cur __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur pts_cur __default_Point)))) ((point_y ((Znth pivot_cur pts_cur __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur)) (PreH13 : (pivot_cur < n_pre)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_permutation pts_l pts_cur )) (PreH16 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> (unique_n + 1 ))
  **  ((pivot_idx_pre) # Int  |-> unique_n)
|--
  “ ((read + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (read + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_19 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (retval: Z)  __default_Point (PreH1 : (retval >= 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur __default_Point)))) ((point_y ((Znth unique_n pts_cur __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur pts_cur __default_Point)))) ((point_y ((Znth pivot_cur pts_cur __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur)) (PreH13 : (pivot_cur < n_pre)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_permutation pts_l pts_cur )) (PreH16 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> (unique_n + 1 ))
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ ((read + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (read + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_20 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (scan >= unique_n)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= scan)) (PreH9 : (scan <= unique_n)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur)) (PreH13 : (pivot_cur < n_pre)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH16 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) (PreH17 : (duplicate <> 0)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ ((read + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (read + 1 )) ”
.

Definition dedup_points_and_find_leftmost_safety_wit_21 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((point_y ((Znth scan pts_cur __default_Point))) = (point_y ((Znth read pts_cur __default_Point))))) (PreH2 : ((point_x ((Znth scan pts_cur __default_Point))) = (point_x ((Znth read pts_cur __default_Point))))) (PreH3 : (scan < unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur)) (PreH15 : (pivot_cur < n_pre)) (PreH16 : (points_in_bound pts_cur )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH18 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ ((read + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (read + 1 )) ”
.

Definition dedup_points_and_find_leftmost_entail_wit_1 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pivot0: Z) (pts_l: (@list Point)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (0 <= pivot0)) (PreH5 : (pivot0 < n_pre)) (PreH6 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_l )
  **  ((pivot_idx_pre) # Int  |-> pivot0)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur 0 0 pivot_cur ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pivot0: Z) (pts_l: (@list Point)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (0 <= pivot0)) (PreH5 : (pivot0 < n_pre)) (PreH6 : (points_in_bound pts_l )) ,
  TT && emp 
|--
  “ (point_dedup_scan_inv pts_l pts_l 0 0 pivot0 ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (pivot0: Z) (pts_l: (@list Point)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (0 <= pivot0)) (PreH5 : (pivot0 < n_pre)) (PreH6 : (points_in_bound pts_l )) ,
  (point_dedup_scan_inv pts_l pts_l 0 0 pivot0 )
.

Definition dedup_points_and_find_leftmost_entail_wit_2 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_cur_2: Z) (unique_n: Z) (read: Z) (pts_cur_2: (@list Point)) (PreH1 : (read < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur_2)) (PreH11 : (pivot_cur_2 < n_pre)) (PreH12 : (points_in_bound pts_cur_2 )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur_2)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur ) ” 
  &&  “ (point_dedup_inner_scan_inv pts_cur unique_n read 0 0 ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (pivot_cur_2: Z) (unique_n: Z) (read: Z) (pts_cur_2: (@list Point)) (PreH1 : (read < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur_2)) (PreH11 : (pivot_cur_2 < n_pre)) (PreH12 : (points_in_bound pts_cur_2 )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) ,
  TT && emp 
|--
  “ (point_dedup_inner_scan_inv pts_cur_2 unique_n read 0 0 ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pivot_cur_2: Z) (unique_n: Z) (read: Z) (pts_cur_2: (@list Point)) (PreH1 : (read < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur_2)) (PreH11 : (pivot_cur_2 < n_pre)) (PreH12 : (points_in_bound pts_cur_2 )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) ,
  (point_dedup_inner_scan_inv pts_cur_2 unique_n read 0 0 )
.

Definition dedup_points_and_find_leftmost_entail_wit_3_1 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point))  __default_Point (PreH1 : ((point_x ((Znth scan pts_cur_2 __default_Point))) <> (point_x ((Znth read pts_cur_2 __default_Point))))) (PreH2 : (scan < unique_n)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= scan)) (PreH10 : (scan <= unique_n)) (PreH11 : (0 <= unique_n)) (PreH12 : (unique_n <= read)) (PreH13 : (0 <= pivot_cur_2)) (PreH14 : (pivot_cur_2 < n_pre)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH17 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur_2)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= (scan + 1 )) ” 
  &&  “ ((scan + 1 ) <= unique_n) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur ) ” 
  &&  “ (point_dedup_inner_scan_inv pts_cur unique_n read (scan + 1 ) duplicate ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point))  __default_Point (PreH1 : ((point_x ((Znth scan pts_cur_2 __default_Point))) <> (point_x ((Znth read pts_cur_2 __default_Point))))) (PreH2 : (scan < unique_n)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= scan)) (PreH10 : (scan <= unique_n)) (PreH11 : (0 <= unique_n)) (PreH12 : (unique_n <= read)) (PreH13 : (0 <= pivot_cur_2)) (PreH14 : (pivot_cur_2 < n_pre)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH17 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) ,
  TT && emp 
|--
  “ (point_dedup_inner_scan_inv pts_cur_2 unique_n read (scan + 1 ) duplicate ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_3_1_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point))  __default_Point (PreH1 : ((point_x ((Znth scan pts_cur_2 __default_Point))) <> (point_x ((Znth read pts_cur_2 __default_Point))))) (PreH2 : (scan < unique_n)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= scan)) (PreH10 : (scan <= unique_n)) (PreH11 : (0 <= unique_n)) (PreH12 : (unique_n <= read)) (PreH13 : (0 <= pivot_cur_2)) (PreH14 : (pivot_cur_2 < n_pre)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH17 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) ,
  (point_dedup_inner_scan_inv pts_cur_2 unique_n read (scan + 1 ) duplicate )
.

Definition dedup_points_and_find_leftmost_entail_wit_3_2 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point))  __default_Point (PreH1 : ((point_y ((Znth scan pts_cur_2 __default_Point))) <> (point_y ((Znth read pts_cur_2 __default_Point))))) (PreH2 : ((point_x ((Znth scan pts_cur_2 __default_Point))) = (point_x ((Znth read pts_cur_2 __default_Point))))) (PreH3 : (scan < unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur_2)) (PreH15 : (pivot_cur_2 < n_pre)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH18 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur_2)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= (scan + 1 )) ” 
  &&  “ ((scan + 1 ) <= unique_n) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur ) ” 
  &&  “ (point_dedup_inner_scan_inv pts_cur unique_n read (scan + 1 ) duplicate ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point))  __default_Point (PreH1 : ((point_y ((Znth scan pts_cur_2 __default_Point))) <> (point_y ((Znth read pts_cur_2 __default_Point))))) (PreH2 : ((point_x ((Znth scan pts_cur_2 __default_Point))) = (point_x ((Znth read pts_cur_2 __default_Point))))) (PreH3 : (scan < unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur_2)) (PreH15 : (pivot_cur_2 < n_pre)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH18 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) ,
  TT && emp 
|--
  “ (point_dedup_inner_scan_inv pts_cur_2 unique_n read (scan + 1 ) duplicate ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_3_2_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point))  __default_Point (PreH1 : ((point_y ((Znth scan pts_cur_2 __default_Point))) <> (point_y ((Znth read pts_cur_2 __default_Point))))) (PreH2 : ((point_x ((Znth scan pts_cur_2 __default_Point))) = (point_x ((Znth read pts_cur_2 __default_Point))))) (PreH3 : (scan < unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur_2)) (PreH15 : (pivot_cur_2 < n_pre)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH18 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) ,
  (point_dedup_inner_scan_inv pts_cur_2 unique_n read (scan + 1 ) duplicate )
.

Definition dedup_points_and_find_leftmost_entail_wit_4_1 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point)) (PreH1 : (read = unique_n)) (PreH2 : (scan >= unique_n)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= scan)) (PreH10 : (scan <= unique_n)) (PreH11 : (0 <= unique_n)) (PreH12 : (unique_n <= read)) (PreH13 : (0 <= pivot_cur_2)) (PreH14 : (pivot_cur_2 < n_pre)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH17 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) (PreH18 : (duplicate = 0)) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur_2)
|--
  (EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ” 
  &&  “ (point_no_dup_prefix pts_cur (unique_n + 1 ) ) ” 
  &&  “ (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) ) ” 
  &&  “ (unique_n = 0) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur))
  ||
  (EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ” 
  &&  “ (point_no_dup_prefix pts_cur (unique_n + 1 ) ) ” 
  &&  “ (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) ) ” 
  &&  “ (point_leftmost_prefix pts_cur pivot_cur unique_n ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur))
.

Definition dedup_points_and_find_leftmost_entail_wit_4_2 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point)) (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : (read <> unique_n)) (PreH3 : (scan >= unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur_2)) (PreH15 : (pivot_cur_2 < n_pre)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH18 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) (PreH19 : (duplicate = 0)) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_cur_2) (unique_n) (read)) )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur_2)
|--
  (EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ” 
  &&  “ (point_no_dup_prefix pts_cur (unique_n + 1 ) ) ” 
  &&  “ (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) ) ” 
  &&  “ (unique_n = 0) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur))
  ||
  (EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ” 
  &&  “ (point_no_dup_prefix pts_cur (unique_n + 1 ) ) ” 
  &&  “ (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) ) ” 
  &&  “ (point_leftmost_prefix pts_cur pivot_cur unique_n ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur))
.

Definition dedup_points_and_find_leftmost_entail_wit_5_1 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur_2)) (PreH11 : (pivot_cur_2 < n_pre)) (PreH12 : (points_in_bound pts_cur_2 )) (PreH13 : (point_permutation pts_l pts_cur_2 )) (PreH14 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur_2 pivot_cur_2 unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> unique_n)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= (read + 1 )) ” 
  &&  “ ((read + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unique_n + 1 )) ” 
  &&  “ ((unique_n + 1 ) <= (read + 1 )) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur (read + 1 ) (unique_n + 1 ) pivot_cur ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur_2)) (PreH11 : (pivot_cur_2 < n_pre)) (PreH12 : (points_in_bound pts_cur_2 )) (PreH13 : (point_permutation pts_l pts_cur_2 )) (PreH14 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur_2 pivot_cur_2 unique_n )) ,
  TT && emp 
|--
  “ (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) (unique_n + 1 ) unique_n ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_5_1_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur_2)) (PreH11 : (pivot_cur_2 < n_pre)) (PreH12 : (points_in_bound pts_cur_2 )) (PreH13 : (point_permutation pts_l pts_cur_2 )) (PreH14 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur_2 pivot_cur_2 unique_n )) ,
  (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) (unique_n + 1 ) unique_n )
.

Definition dedup_points_and_find_leftmost_entail_wit_5_2 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur_2)) (PreH11 : (pivot_cur_2 < n_pre)) (PreH12 : (points_in_bound pts_cur_2 )) (PreH13 : (point_permutation pts_l pts_cur_2 )) (PreH14 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (unique_n = 0)) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> unique_n)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= (read + 1 )) ” 
  &&  “ ((read + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unique_n + 1 )) ” 
  &&  “ ((unique_n + 1 ) <= (read + 1 )) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur (read + 1 ) (unique_n + 1 ) pivot_cur ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur_2)) (PreH11 : (pivot_cur_2 < n_pre)) (PreH12 : (points_in_bound pts_cur_2 )) (PreH13 : (point_permutation pts_l pts_cur_2 )) (PreH14 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (unique_n = 0)) ,
  TT && emp 
|--
  “ (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) (unique_n + 1 ) unique_n ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_5_2_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (PreH1 : (unique_n = 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur_2)) (PreH11 : (pivot_cur_2 < n_pre)) (PreH12 : (points_in_bound pts_cur_2 )) (PreH13 : (point_permutation pts_l pts_cur_2 )) (PreH14 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (unique_n = 0)) ,
  (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) (unique_n + 1 ) unique_n )
.

Definition dedup_points_and_find_leftmost_entail_wit_5_3 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (retval: Z)  __default_Point (PreH1 : (retval < 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur_2 __default_Point)))) ((point_y ((Znth unique_n pts_cur_2 __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur_2 pts_cur_2 __default_Point)))) ((point_y ((Znth pivot_cur_2 pts_cur_2 __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur_2)) (PreH13 : (pivot_cur_2 < n_pre)) (PreH14 : (points_in_bound pts_cur_2 )) (PreH15 : (point_permutation pts_l pts_cur_2 )) (PreH16 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur_2 pivot_cur_2 unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> unique_n)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= (read + 1 )) ” 
  &&  “ ((read + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unique_n + 1 )) ” 
  &&  “ ((unique_n + 1 ) <= (read + 1 )) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur (read + 1 ) (unique_n + 1 ) pivot_cur ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (retval: Z)  __default_Point (PreH1 : (retval < 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur_2 __default_Point)))) ((point_y ((Znth unique_n pts_cur_2 __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur_2 pts_cur_2 __default_Point)))) ((point_y ((Znth pivot_cur_2 pts_cur_2 __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur_2)) (PreH13 : (pivot_cur_2 < n_pre)) (PreH14 : (points_in_bound pts_cur_2 )) (PreH15 : (point_permutation pts_l pts_cur_2 )) (PreH16 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur_2 pivot_cur_2 unique_n )) ,
  TT && emp 
|--
  “ (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) (unique_n + 1 ) unique_n ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_5_3_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (retval: Z)  __default_Point (PreH1 : (retval < 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur_2 __default_Point)))) ((point_y ((Znth unique_n pts_cur_2 __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur_2 pts_cur_2 __default_Point)))) ((point_y ((Znth pivot_cur_2 pts_cur_2 __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur_2)) (PreH13 : (pivot_cur_2 < n_pre)) (PreH14 : (points_in_bound pts_cur_2 )) (PreH15 : (point_permutation pts_l pts_cur_2 )) (PreH16 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur_2 pivot_cur_2 unique_n )) ,
  (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) (unique_n + 1 ) unique_n )
.

Definition dedup_points_and_find_leftmost_entail_wit_5_4 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (retval: Z)  __default_Point (PreH1 : (retval >= 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur_2 __default_Point)))) ((point_y ((Znth unique_n pts_cur_2 __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur_2 pts_cur_2 __default_Point)))) ((point_y ((Znth pivot_cur_2 pts_cur_2 __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur_2)) (PreH13 : (pivot_cur_2 < n_pre)) (PreH14 : (points_in_bound pts_cur_2 )) (PreH15 : (point_permutation pts_l pts_cur_2 )) (PreH16 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur_2 pivot_cur_2 unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur_2)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= (read + 1 )) ” 
  &&  “ ((read + 1 ) <= n_pre) ” 
  &&  “ (0 <= (unique_n + 1 )) ” 
  &&  “ ((unique_n + 1 ) <= (read + 1 )) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur (read + 1 ) (unique_n + 1 ) pivot_cur ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (retval: Z)  __default_Point (PreH1 : (retval >= 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur_2 __default_Point)))) ((point_y ((Znth unique_n pts_cur_2 __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur_2 pts_cur_2 __default_Point)))) ((point_y ((Znth pivot_cur_2 pts_cur_2 __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur_2)) (PreH13 : (pivot_cur_2 < n_pre)) (PreH14 : (points_in_bound pts_cur_2 )) (PreH15 : (point_permutation pts_l pts_cur_2 )) (PreH16 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur_2 pivot_cur_2 unique_n )) ,
  TT && emp 
|--
  “ (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) (unique_n + 1 ) pivot_cur_2 ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_5_4_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pts_cur_2: (@list Point)) (pivot_cur_2: Z) (read: Z) (unique_n: Z) (retval: Z)  __default_Point (PreH1 : (retval >= 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth unique_n pts_cur_2 __default_Point)))) ((point_y ((Znth unique_n pts_cur_2 __default_Point)))))) ((point_mk ((point_x ((Znth pivot_cur_2 pts_cur_2 __default_Point)))) ((point_y ((Znth pivot_cur_2 pts_cur_2 __default_Point))))))))) (PreH3 : (unique_n <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur_2)) (PreH13 : (pivot_cur_2 < n_pre)) (PreH14 : (points_in_bound pts_cur_2 )) (PreH15 : (point_permutation pts_l pts_cur_2 )) (PreH16 : (point_no_dup_prefix pts_cur_2 (unique_n + 1 ) )) (PreH17 : (point_prefix_represents_range pts_cur_2 (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH18 : (point_leftmost_prefix pts_cur_2 pivot_cur_2 unique_n )) ,
  (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) (unique_n + 1 ) pivot_cur_2 )
.

Definition dedup_points_and_find_leftmost_entail_wit_5_5 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point)) (PreH1 : (scan >= unique_n)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= scan)) (PreH9 : (scan <= unique_n)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur_2)) (PreH13 : (pivot_cur_2 < n_pre)) (PreH14 : (points_in_bound pts_cur_2 )) (PreH15 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH16 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) (PreH17 : (duplicate <> 0)) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur_2)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= (read + 1 )) ” 
  &&  “ ((read + 1 ) <= n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= (read + 1 )) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur (read + 1 ) unique_n pivot_cur ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point)) (PreH1 : (scan >= unique_n)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= scan)) (PreH9 : (scan <= unique_n)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur_2)) (PreH13 : (pivot_cur_2 < n_pre)) (PreH14 : (points_in_bound pts_cur_2 )) (PreH15 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH16 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) (PreH17 : (duplicate <> 0)) ,
  TT && emp 
|--
  “ (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) unique_n pivot_cur_2 ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_5_5_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point)) (PreH1 : (scan >= unique_n)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= scan)) (PreH9 : (scan <= unique_n)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur_2)) (PreH13 : (pivot_cur_2 < n_pre)) (PreH14 : (points_in_bound pts_cur_2 )) (PreH15 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH16 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) (PreH17 : (duplicate <> 0)) ,
  (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) unique_n pivot_cur_2 )
.

Definition dedup_points_and_find_leftmost_entail_wit_5_6 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point))  __default_Point (PreH1 : ((point_y ((Znth scan pts_cur_2 __default_Point))) = (point_y ((Znth read pts_cur_2 __default_Point))))) (PreH2 : ((point_x ((Znth scan pts_cur_2 __default_Point))) = (point_x ((Znth read pts_cur_2 __default_Point))))) (PreH3 : (scan < unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur_2)) (PreH15 : (pivot_cur_2 < n_pre)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH18 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur_2 )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur_2)
|--
  EX (pivot_cur: Z)  (pts_cur: (@list Point)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= (read + 1 )) ” 
  &&  “ ((read + 1 ) <= n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= (read + 1 )) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur (read + 1 ) unique_n pivot_cur ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point))  __default_Point (PreH1 : ((point_y ((Znth scan pts_cur_2 __default_Point))) = (point_y ((Znth read pts_cur_2 __default_Point))))) (PreH2 : ((point_x ((Znth scan pts_cur_2 __default_Point))) = (point_x ((Znth read pts_cur_2 __default_Point))))) (PreH3 : (scan < unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur_2)) (PreH15 : (pivot_cur_2 < n_pre)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH18 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) ,
  TT && emp 
|--
  “ (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) unique_n pivot_cur_2 ) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_entail_wit_5_6_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur_2: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur_2: (@list Point))  __default_Point (PreH1 : ((point_y ((Znth scan pts_cur_2 __default_Point))) = (point_y ((Znth read pts_cur_2 __default_Point))))) (PreH2 : ((point_x ((Znth scan pts_cur_2 __default_Point))) = (point_x ((Znth read pts_cur_2 __default_Point))))) (PreH3 : (scan < unique_n)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : ((Zlength (pts_cur_2)) = n_pre)) (PreH8 : (0 <= read)) (PreH9 : (read < n_pre)) (PreH10 : (0 <= scan)) (PreH11 : (scan <= unique_n)) (PreH12 : (0 <= unique_n)) (PreH13 : (unique_n <= read)) (PreH14 : (0 <= pivot_cur_2)) (PreH15 : (pivot_cur_2 < n_pre)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_dedup_scan_inv pts_l pts_cur_2 read unique_n pivot_cur_2 )) (PreH18 : (point_dedup_inner_scan_inv pts_cur_2 unique_n read scan duplicate )) ,
  (point_dedup_scan_inv pts_l pts_cur_2 (read + 1 ) unique_n pivot_cur_2 )
.

Definition dedup_points_and_find_leftmost_return_wit_1 := 
(
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_cur: Z) (unique_n: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (read >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  EX (pivot_out: Z)  (pts_out: (@list Point)) ,
  “ (1 <= unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (0 <= pivot_out) ” 
  &&  “ (pivot_out < unique_n) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_dedup_result pts_l pts_out unique_n pivot_out ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  ((pivot_idx_pre) # Int  |-> pivot_out)
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (pivot_cur: Z) (unique_n: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (read >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) ,
  TT && emp 
|--
  “ (point_dedup_result pts_l pts_cur unique_n pivot_cur ) ” 
  &&  “ (pivot_cur < unique_n) ” 
  &&  “ (1 <= unique_n) ”
  &&  emp
).

Definition dedup_points_and_find_leftmost_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pivot_cur: Z) (unique_n: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (read >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) ,
  (point_dedup_result pts_l pts_cur unique_n pivot_cur )
.

Definition dedup_points_and_find_leftmost_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pivot_cur: Z) (unique_n: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (read >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) ,
  (pivot_cur < unique_n)
.

Definition dedup_points_and_find_leftmost_return_wit_1_split_goal_3 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pivot_cur: Z) (unique_n: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (read >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read <= n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) ,
  (1 <= unique_n)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_1 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (scan < unique_n)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= scan)) (PreH9 : (scan <= unique_n)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur)) (PreH13 : (pivot_cur < n_pre)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH16 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (scan < unique_n) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= scan) ” 
  &&  “ (scan <= unique_n) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur ) ” 
  &&  “ (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate ) ”
  &&  ((&(((pts_pre + (scan * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth scan pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre scan 0 n_pre pts_cur )
  **  ((&(((pts_pre + (scan * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth scan pts_cur __default_Point))))
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_2 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (scan < unique_n)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= scan)) (PreH9 : (scan <= unique_n)) (PreH10 : (0 <= unique_n)) (PreH11 : (unique_n <= read)) (PreH12 : (0 <= pivot_cur)) (PreH13 : (pivot_cur < n_pre)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH16 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (scan < unique_n) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= scan) ” 
  &&  “ (scan <= unique_n) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur ) ” 
  &&  “ (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate ) ”
  &&  ((&(((pts_pre + (read * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth read pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre read 0 n_pre pts_cur )
  **  ((&(((pts_pre + (read * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth read pts_cur __default_Point))))
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_3 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((point_x ((Znth scan pts_cur __default_Point))) = (point_x ((Znth read pts_cur __default_Point))))) (PreH2 : (scan < unique_n)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= scan)) (PreH10 : (scan <= unique_n)) (PreH11 : (0 <= unique_n)) (PreH12 : (unique_n <= read)) (PreH13 : (0 <= pivot_cur)) (PreH14 : (pivot_cur < n_pre)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH17 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ ((point_x ((Znth scan pts_cur __default_Point))) = (point_x ((Znth read pts_cur __default_Point)))) ” 
  &&  “ (scan < unique_n) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= scan) ” 
  &&  “ (scan <= unique_n) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur ) ” 
  &&  “ (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate ) ”
  &&  ((&(((pts_pre + (scan * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth scan pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre scan 0 n_pre pts_cur )
  **  ((&(((pts_pre + (scan * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth scan pts_cur __default_Point))))
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_4 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((point_x ((Znth scan pts_cur __default_Point))) = (point_x ((Znth read pts_cur __default_Point))))) (PreH2 : (scan < unique_n)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= scan)) (PreH10 : (scan <= unique_n)) (PreH11 : (0 <= unique_n)) (PreH12 : (unique_n <= read)) (PreH13 : (0 <= pivot_cur)) (PreH14 : (pivot_cur < n_pre)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH17 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ ((point_x ((Znth scan pts_cur __default_Point))) = (point_x ((Znth read pts_cur __default_Point)))) ” 
  &&  “ (scan < unique_n) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= scan) ” 
  &&  “ (scan <= unique_n) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur ) ” 
  &&  “ (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate ) ”
  &&  ((&(((pts_pre + (read * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth read pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre read 0 n_pre pts_cur )
  **  ((&(((pts_pre + (read * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth read pts_cur __default_Point))))
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_5_pure := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (read <> unique_n)) (PreH2 : (scan >= unique_n)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= scan)) (PreH10 : (scan <= unique_n)) (PreH11 : (0 <= unique_n)) (PreH12 : (unique_n <= read)) (PreH13 : (0 <= pivot_cur)) (PreH14 : (pivot_cur < n_pre)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH17 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) (PreH18 : (duplicate = 0)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Ptr  |-> pivot_idx_pre)
  **  ((( &( "read" ) )) # Int  |-> read)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "duplicate" ) )) # Int  |-> duplicate)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (0 <= unique_n) ” 
  &&  “ (unique_n < n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (unique_n <> read) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ”
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_5_aux := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (duplicate: Z) (pivot_cur: Z) (unique_n: Z) (scan: Z) (read: Z) (pts_cur: (@list Point)) (PreH1 : (read <> unique_n)) (PreH2 : (scan >= unique_n)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : ((Zlength (pts_cur)) = n_pre)) (PreH7 : (0 <= read)) (PreH8 : (read < n_pre)) (PreH9 : (0 <= scan)) (PreH10 : (scan <= unique_n)) (PreH11 : (0 <= unique_n)) (PreH12 : (unique_n <= read)) (PreH13 : (0 <= pivot_cur)) (PreH14 : (pivot_cur < n_pre)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur )) (PreH17 : (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate )) (PreH18 : (duplicate = 0)) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (0 <= unique_n) ” 
  &&  “ (unique_n < n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (unique_n <> read) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (read <> unique_n) ” 
  &&  “ (scan >= unique_n) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= scan) ” 
  &&  “ (scan <= unique_n) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_dedup_scan_inv pts_l pts_cur read unique_n pivot_cur ) ” 
  &&  “ (point_dedup_inner_scan_inv pts_cur unique_n read scan duplicate ) ” 
  &&  “ (duplicate = 0) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_5 := dedup_points_and_find_leftmost_partial_solve_wit_5_pure -> dedup_points_and_find_leftmost_partial_solve_wit_5_aux.

Definition dedup_points_and_find_leftmost_partial_solve_wit_6 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z)  __default_Point (PreH1 : (unique_n <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (unique_n <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ” 
  &&  “ (point_no_dup_prefix pts_cur (unique_n + 1 ) ) ” 
  &&  “ (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) ) ” 
  &&  “ (point_leftmost_prefix pts_cur pivot_cur unique_n ) ”
  &&  ((&(((pts_pre + (unique_n * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth unique_n pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre unique_n 0 n_pre pts_cur )
  **  ((&(((pts_pre + (unique_n * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth unique_n pts_cur __default_Point))))
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_7 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z)  __default_Point (PreH1 : (unique_n <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (unique_n <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ” 
  &&  “ (point_no_dup_prefix pts_cur (unique_n + 1 ) ) ” 
  &&  “ (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) ) ” 
  &&  “ (point_leftmost_prefix pts_cur pivot_cur unique_n ) ”
  &&  ((&(((pts_pre + (unique_n * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth unique_n pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre unique_n 0 n_pre pts_cur )
  **  ((&(((pts_pre + (unique_n * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth unique_n pts_cur __default_Point))))
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_8 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z)  __default_Point (PreH1 : (unique_n <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (unique_n <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ” 
  &&  “ (point_no_dup_prefix pts_cur (unique_n + 1 ) ) ” 
  &&  “ (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) ) ” 
  &&  “ (point_leftmost_prefix pts_cur pivot_cur unique_n ) ”
  &&  ((&(((pts_pre + (pivot_cur * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth pivot_cur pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre pivot_cur 0 n_pre pts_cur )
  **  ((&(((pts_pre + (pivot_cur * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth pivot_cur pts_cur __default_Point))))
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_9 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z)  __default_Point (PreH1 : (unique_n <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (unique_n <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ” 
  &&  “ (point_no_dup_prefix pts_cur (unique_n + 1 ) ) ” 
  &&  “ (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) ) ” 
  &&  “ (point_leftmost_prefix pts_cur pivot_cur unique_n ) ”
  &&  ((&(((pts_pre + (pivot_cur * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth pivot_cur pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre pivot_cur 0 n_pre pts_cur )
  **  ((&(((pts_pre + (pivot_cur * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth pivot_cur pts_cur __default_Point))))
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

Definition dedup_points_and_find_leftmost_partial_solve_wit_10 := 
forall (pivot_idx_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_cur: (@list Point)) (pivot_cur: Z) (read: Z) (unique_n: Z) (PreH1 : (unique_n <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= read)) (PreH7 : (read < n_pre)) (PreH8 : (0 <= unique_n)) (PreH9 : (unique_n <= read)) (PreH10 : (0 <= pivot_cur)) (PreH11 : (pivot_cur < n_pre)) (PreH12 : (points_in_bound pts_cur )) (PreH13 : (point_permutation pts_l pts_cur )) (PreH14 : (point_no_dup_prefix pts_cur (unique_n + 1 ) )) (PreH15 : (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) )) (PreH16 : (point_leftmost_prefix pts_cur pivot_cur unique_n )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
|--
  “ (unique_n <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_cur)) = n_pre) ” 
  &&  “ (0 <= read) ” 
  &&  “ (read < n_pre) ” 
  &&  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= read) ” 
  &&  “ (0 <= pivot_cur) ” 
  &&  “ (pivot_cur < n_pre) ” 
  &&  “ (points_in_bound pts_cur ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ” 
  &&  “ (point_no_dup_prefix pts_cur (unique_n + 1 ) ) ” 
  &&  “ (point_prefix_represents_range pts_cur (unique_n + 1 ) (unique_n + 1 ) (read + 1 ) ) ” 
  &&  “ (point_leftmost_prefix pts_cur pivot_cur unique_n ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
  **  ((pivot_idx_pre) # Int  |-> pivot_cur)
.

(*----- Function graham_scan_dedup -----*)

Definition graham_scan_dedup_safety_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) ,
  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_dedup_safety_wit_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) ,
  ((( &( "pivot_idx" ) )) # Int  |->_)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_dedup_safety_wit_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) (PreH6 : ((Zlength (pts_dedup)) = n_pre)) (PreH7 : (points_in_bound pts_dedup )) (PreH8 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH9 : (0 <= pivot_out)) (PreH10 : (pivot_out < unique_n)) (PreH11 : (unique_n <= n_pre)) (PreH12 : (2 <= unique_n)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_out)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_dedup_safety_wit_4 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) (PreH6 : ((Zlength (pts_dedup)) = n_pre)) (PreH7 : (points_in_bound pts_dedup )) (PreH8 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH9 : (0 <= pivot_out)) (PreH10 : (pivot_out < unique_n)) (PreH11 : (unique_n <= n_pre)) (PreH12 : (2 <= unique_n)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_out)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_dedup_safety_wit_5 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z) (PreH1 : (pivot_out <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : (points_in_bound pts_l )) (PreH6 : (points_not_all_same pts_l )) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : (points_in_bound pts_dedup )) (PreH9 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH10 : (0 <= pivot_out)) (PreH11 : (pivot_out < unique_n)) (PreH12 : (unique_n <= n_pre)) (PreH13 : (2 <= unique_n)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_out)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_dedup_safety_wit_6 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z) (PreH1 : ((Zlength (pts_dedup)) = n_pre)) (PreH2 : (pivot_out <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : (points_in_bound pts_l )) (PreH7 : (points_not_all_same pts_l )) (PreH8 : ((Zlength (pts_dedup)) = n_pre)) (PreH9 : (points_in_bound pts_dedup )) (PreH10 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH11 : (0 <= pivot_out)) (PreH12 : (pivot_out < unique_n)) (PreH13 : (unique_n <= n_pre)) (PreH14 : (2 <= unique_n)) ,
  ((( &( "gx" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre (point_swap (pts_dedup) (0) (pivot_out)) )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_out)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_dedup_safety_wit_7 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z) (PreH1 : (pivot_out = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : (points_in_bound pts_l )) (PreH6 : (points_not_all_same pts_l )) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : (points_in_bound pts_dedup )) (PreH9 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH10 : (0 <= pivot_out)) (PreH11 : (pivot_out < unique_n)) (PreH12 : (unique_n <= n_pre)) (PreH13 : (2 <= unique_n)) ,
  ((( &( "gx" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_out)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_dedup_safety_wit_8 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : ((Zlength (pts_dedup)) = n_pre)) (PreH2 : (pivot_out <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : (points_in_bound pts_l )) (PreH7 : (points_not_all_same pts_l )) (PreH8 : ((Zlength (pts_dedup)) = n_pre)) (PreH9 : (points_in_bound pts_dedup )) (PreH10 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH11 : (0 <= pivot_out)) (PreH12 : (pivot_out < unique_n)) (PreH13 : (unique_n <= n_pre)) (PreH14 : (2 <= unique_n)) ,
  ((( &( "gy" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre (point_swap (pts_dedup) (0) (pivot_out)) )
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_out)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_dedup_safety_wit_9 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : (pivot_out = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : (points_in_bound pts_l )) (PreH6 : (points_not_all_same pts_l )) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : (points_in_bound pts_dedup )) (PreH9 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH10 : (0 <= pivot_out)) (PreH11 : (pivot_out < unique_n)) (PreH12 : (unique_n <= n_pre)) (PreH13 : (2 <= unique_n)) ,
  ((( &( "gy" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_dedup )
  **  ((( &( "gx" ) )) # Int  |-> (point_x ((Znth 0 pts_dedup __default_Point))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_out)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition graham_scan_dedup_safety_wit_10 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (unique_prefix: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point (PreH1 : (2 <= unique_n)) (PreH2 : (unique_n <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (1 <= (unique_n - 1 ))) (PreH5 : ((unique_n - 1 ) < INT_MAX)) (PreH6 : (((unique_n - 1 ) + 1 ) <= n_pre)) (PreH7 : (pivot0 = (point_mk (gx) (gy)))) (PreH8 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH9 : ((Zlength (pts_dedup)) = n_pre)) (PreH10 : ((Zlength (pts_pivot)) = n_pre)) (PreH11 : ((Zlength (unique_prefix)) = unique_n)) (PreH12 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH13 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH14 : (points_in_bound pts_dedup )) (PreH15 : (points_in_bound pts_pivot )) (PreH16 : (points_in_bound unique_prefix )) (PreH17 : (point_in_bound pivot0 )) (PreH18 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH19 : (point_no_dup_prefix pts_pivot unique_n )) (PreH20 : (leftmost pivot0 unique_prefix )) (PreH21 : (point_polar_cmp_safe_range pivot0 unique_prefix 1 (unique_n - 1 ) )) (PreH22 : (((Znth 0 pts_pivot __default_Point).(x) ) = gx)) (PreH23 : (((Znth 0 pts_pivot __default_Point).(y) ) = gy)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.full pts_pre unique_n unique_prefix )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ ((unique_n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (unique_n - 1 )) ”
.

Definition graham_scan_dedup_safety_wit_11 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (unique_prefix: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point (PreH1 : (2 <= unique_n)) (PreH2 : (unique_n <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (1 <= (unique_n - 1 ))) (PreH5 : ((unique_n - 1 ) < INT_MAX)) (PreH6 : (((unique_n - 1 ) + 1 ) <= n_pre)) (PreH7 : (pivot0 = (point_mk (gx) (gy)))) (PreH8 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH9 : ((Zlength (pts_dedup)) = n_pre)) (PreH10 : ((Zlength (pts_pivot)) = n_pre)) (PreH11 : ((Zlength (unique_prefix)) = unique_n)) (PreH12 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH13 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH14 : (points_in_bound pts_dedup )) (PreH15 : (points_in_bound pts_pivot )) (PreH16 : (points_in_bound unique_prefix )) (PreH17 : (point_in_bound pivot0 )) (PreH18 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH19 : (point_no_dup_prefix pts_pivot unique_n )) (PreH20 : (leftmost pivot0 unique_prefix )) (PreH21 : (point_polar_cmp_safe_range pivot0 unique_prefix 1 (unique_n - 1 ) )) (PreH22 : (((Znth 0 pts_pivot __default_Point).(x) ) = gx)) (PreH23 : (((Znth 0 pts_pivot __default_Point).(y) ) = gy)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.full pts_pre unique_n unique_prefix )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_dedup_safety_wit_12 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (unique_prefix: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point (PreH1 : (2 <= unique_n)) (PreH2 : (unique_n <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (1 <= (unique_n - 1 ))) (PreH5 : ((unique_n - 1 ) < INT_MAX)) (PreH6 : (((unique_n - 1 ) + 1 ) <= n_pre)) (PreH7 : (pivot0 = (point_mk (gx) (gy)))) (PreH8 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH9 : ((Zlength (pts_dedup)) = n_pre)) (PreH10 : ((Zlength (pts_pivot)) = n_pre)) (PreH11 : ((Zlength (unique_prefix)) = unique_n)) (PreH12 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH13 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH14 : (points_in_bound pts_dedup )) (PreH15 : (points_in_bound pts_pivot )) (PreH16 : (points_in_bound unique_prefix )) (PreH17 : (point_in_bound pivot0 )) (PreH18 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH19 : (point_no_dup_prefix pts_pivot unique_n )) (PreH20 : (leftmost pivot0 unique_prefix )) (PreH21 : (point_polar_cmp_safe_range pivot0 unique_prefix 1 (unique_n - 1 ) )) (PreH22 : (((Znth 0 pts_pivot __default_Point).(x) ) = gx)) (PreH23 : (((Znth 0 pts_pivot __default_Point).(y) ) = gy)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.full pts_pre unique_n unique_prefix )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_dedup_safety_wit_13 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (unique_prefix: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (pts_out: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_out)) = unique_n)) (PreH2 : (points_in_bound pts_out )) (PreH3 : (leftmost (point_mk (gx) (gy)) pts_out )) (PreH4 : (point_permutation unique_prefix pts_out )) (PreH5 : (point_same_outside_range unique_prefix pts_out 1 (unique_n - 1 ) )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx) (gy)) pts_out 1 (unique_n - 1 ) )) (PreH7 : (point_sorted_range (point_mk (gx) (gy)) pts_out 1 (unique_n - 1 ) )) (PreH8 : (2 <= unique_n)) (PreH9 : (unique_n <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (1 <= (unique_n - 1 ))) (PreH12 : ((unique_n - 1 ) < INT_MAX)) (PreH13 : (((unique_n - 1 ) + 1 ) <= n_pre)) (PreH14 : (pivot0 = (point_mk (gx) (gy)))) (PreH15 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH16 : ((Zlength (pts_dedup)) = n_pre)) (PreH17 : ((Zlength (pts_pivot)) = n_pre)) (PreH18 : ((Zlength (unique_prefix)) = unique_n)) (PreH19 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH20 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH21 : (points_in_bound pts_dedup )) (PreH22 : (points_in_bound pts_pivot )) (PreH23 : (points_in_bound unique_prefix )) (PreH24 : (point_in_bound pivot0 )) (PreH25 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH26 : (point_no_dup_prefix pts_pivot unique_n )) (PreH27 : (leftmost pivot0 unique_prefix )) (PreH28 : (point_polar_cmp_safe_range pivot0 unique_prefix 1 (unique_n - 1 ) )) (PreH29 : (((Znth 0 pts_pivot __default_Point).(x) ) = gx)) (PreH30 : (((Znth 0 pts_pivot __default_Point).(y) ) = gy)) ,
  ((( &( "tail" ) )) # Ptr  |->_)
  **  (PointArray.full pts_pre unique_n pts_out )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_dedup_safety_wit_14 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (unique_prefix: (@list Point)) (tail_sorted: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (tail: Z) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point (PreH1 : (tail = (pts_pre + (1 * sizeof( "Point" ))))) (PreH2 : (2 <= unique_n)) (PreH3 : (unique_n <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (pivot0 = (point_mk (gx) (gy)))) (PreH6 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : ((Zlength (pts_sorted)) = unique_n)) (PreH9 : ((Zlength (unique_prefix)) = unique_n)) (PreH10 : ((Zlength (tail_sorted)) = (unique_n - 1 ))) (PreH11 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH12 : (tail_sorted = (sublist (1) (unique_n) (pts_sorted)))) (PreH13 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH14 : ((unique_n - 1 ) = (Zlength (tail_sorted)))) (PreH15 : (points_in_bound pts_sorted )) (PreH16 : (points_in_bound tail_sorted )) (PreH17 : (point_in_bound pivot0 )) (PreH18 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH19 : (leftmost pivot0 pts_sorted )) (PreH20 : (point_permutation unique_prefix pts_sorted )) (PreH21 : (point_sorted_range (point_mk (gx) (gy)) pts_sorted 1 (unique_n - 1 ) )) (PreH22 : (point_polar_sorted pivot0 tail_sorted )) (PreH23 : (leftmost pivot0 (rev (tail_sorted)) )) (PreH24 : (((Znth 0 pts_sorted __default_Point).(x) ) = gx)) (PreH25 : (((Znth 0 pts_sorted __default_Point).(y) ) = gy)) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (store_point pts_pre pivot0 )
  **  (PointArray.full tail (unique_n - 1 ) tail_sorted )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_seg hull_pre 0 ((unique_n - 1 ) + 1 ) )
  **  (PointArray.undef_seg hull_pre ((unique_n - 1 ) + 1 ) n_pre )
|--
  “ ((unique_n - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (unique_n - 1 )) ”
.

Definition graham_scan_dedup_safety_wit_15 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (unique_prefix: (@list Point)) (tail_sorted: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (tail: Z) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point (PreH1 : (tail = (pts_pre + (1 * sizeof( "Point" ))))) (PreH2 : (2 <= unique_n)) (PreH3 : (unique_n <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (pivot0 = (point_mk (gx) (gy)))) (PreH6 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : ((Zlength (pts_sorted)) = unique_n)) (PreH9 : ((Zlength (unique_prefix)) = unique_n)) (PreH10 : ((Zlength (tail_sorted)) = (unique_n - 1 ))) (PreH11 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH12 : (tail_sorted = (sublist (1) (unique_n) (pts_sorted)))) (PreH13 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH14 : ((unique_n - 1 ) = (Zlength (tail_sorted)))) (PreH15 : (points_in_bound pts_sorted )) (PreH16 : (points_in_bound tail_sorted )) (PreH17 : (point_in_bound pivot0 )) (PreH18 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH19 : (leftmost pivot0 pts_sorted )) (PreH20 : (point_permutation unique_prefix pts_sorted )) (PreH21 : (point_sorted_range (point_mk (gx) (gy)) pts_sorted 1 (unique_n - 1 ) )) (PreH22 : (point_polar_sorted pivot0 tail_sorted )) (PreH23 : (leftmost pivot0 (rev (tail_sorted)) )) (PreH24 : (((Znth 0 pts_sorted __default_Point).(x) ) = gx)) (PreH25 : (((Znth 0 pts_sorted __default_Point).(y) ) = gy)) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (store_point pts_pre pivot0 )
  **  (PointArray.full tail (unique_n - 1 ) tail_sorted )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_seg hull_pre 0 ((unique_n - 1 ) + 1 ) )
  **  (PointArray.undef_seg hull_pre ((unique_n - 1 ) + 1 ) n_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition graham_scan_dedup_entail_wit_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_out: Z) (pts_out: (@list Point)) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval <= n_pre)) (PreH3 : ((Zlength (pts_out)) = n_pre)) (PreH4 : (0 <= pivot_out)) (PreH5 : (pivot_out < retval)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (point_dedup_result pts_l pts_out retval pivot_out )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : (points_in_bound pts_l )) (PreH12 : (points_not_all_same pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  EX (pts_dedup: (@list Point)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (points_not_all_same pts_l ) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ (points_in_bound pts_dedup ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup retval pivot_out ) ” 
  &&  “ (0 <= pivot_out) ” 
  &&  “ (pivot_out < retval) ” 
  &&  “ (retval <= n_pre) ” 
  &&  “ (2 <= retval) ”
  &&  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (pivot_out: Z) (pts_out: (@list Point)) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval <= n_pre)) (PreH3 : ((Zlength (pts_out)) = n_pre)) (PreH4 : (0 <= pivot_out)) (PreH5 : (pivot_out < retval)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (point_dedup_result pts_l pts_out retval pivot_out )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : (points_in_bound pts_l )) (PreH12 : (points_not_all_same pts_l )) ,
  TT && emp 
|--
  “ (2 <= retval) ”
  &&  emp
).

Definition graham_scan_dedup_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pivot_out: Z) (pts_out: (@list Point)) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval <= n_pre)) (PreH3 : ((Zlength (pts_out)) = n_pre)) (PreH4 : (0 <= pivot_out)) (PreH5 : (pivot_out < retval)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (point_dedup_result pts_l pts_out retval pivot_out )) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : (points_in_bound pts_l )) (PreH12 : (points_not_all_same pts_l )) ,
  (2 <= retval)
.

Definition graham_scan_dedup_entail_wit_2_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : (pivot_out = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : (points_in_bound pts_l )) (PreH6 : (points_not_all_same pts_l )) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : (points_in_bound pts_dedup )) (PreH9 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH10 : (0 <= pivot_out)) (PreH11 : (pivot_out < unique_n)) (PreH12 : (unique_n <= n_pre)) (PreH13 : (2 <= unique_n)) ,
  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  EX (suffix: (@list Point))  (unique_prefix: (@list Point))  (pts_dedup_2: (@list Point))  (pts_pivot: (@list Point))  (pivot0: Point) ,
  “ (2 <= unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (1 <= (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) < INT_MAX) ” 
  &&  “ (((unique_n - 1 ) + 1 ) <= n_pre) ” 
  &&  “ (pivot0 = (point_mk ((point_x ((Znth 0 pts_dedup __default_Point)))) ((point_y ((Znth 0 pts_dedup __default_Point)))))) ” 
  &&  “ (pts_pivot = (point_swap (pts_dedup_2) (0) (pivot_out))) ” 
  &&  “ ((Zlength (pts_dedup_2)) = n_pre) ” 
  &&  “ ((Zlength (pts_pivot)) = n_pre) ” 
  &&  “ ((Zlength (unique_prefix)) = unique_n) ” 
  &&  “ (unique_prefix = (sublist (0) (unique_n) (pts_pivot))) ” 
  &&  “ (suffix = (sublist (unique_n) (n_pre) (pts_pivot))) ” 
  &&  “ (points_in_bound pts_dedup_2 ) ” 
  &&  “ (points_in_bound pts_pivot ) ” 
  &&  “ (points_in_bound unique_prefix ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup_2 unique_n pivot_out ) ” 
  &&  “ (point_no_dup_prefix pts_pivot unique_n ) ” 
  &&  “ (leftmost pivot0 unique_prefix ) ” 
  &&  “ (point_polar_cmp_safe_range pivot0 unique_prefix 1 (unique_n - 1 ) ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = (point_x ((Znth 0 pts_dedup __default_Point)))) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = (point_y ((Znth 0 pts_dedup __default_Point)))) ”
  &&  (PointArray.full pts_pre unique_n unique_prefix )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_full hull_pre n_pre )
) \/
(
forall (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : (pivot_out = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : (points_in_bound pts_l )) (PreH6 : (points_not_all_same pts_l )) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : (points_in_bound pts_dedup )) (PreH9 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH10 : (0 <= pivot_out)) (PreH11 : (pivot_out < unique_n)) (PreH12 : (unique_n <= n_pre)) (PreH13 : (2 <= unique_n)) ,
  (PointArray.full pts_pre n_pre pts_dedup )
|--
  EX (pts_dedup_2: (@list Point)) ,
  “ (2 <= unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (1 <= (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) < INT_MAX) ” 
  &&  “ (((unique_n - 1 ) + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pts_dedup_2)) = n_pre) ” 
  &&  “ ((Zlength ((point_swap (pts_dedup_2) (0) (pivot_out)))) = n_pre) ” 
  &&  “ ((Zlength ((sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))))) = unique_n) ” 
  &&  “ (points_in_bound pts_dedup_2 ) ” 
  &&  “ (points_in_bound (point_swap (pts_dedup_2) (0) (pivot_out)) ) ” 
  &&  “ (points_in_bound (sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))) ) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth 0 pts_dedup __default_Point)))) ((point_y ((Znth 0 pts_dedup __default_Point))))) ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup_2 unique_n pivot_out ) ” 
  &&  “ (point_no_dup_prefix (point_swap (pts_dedup_2) (0) (pivot_out)) unique_n ) ” 
  &&  “ (leftmost (point_mk ((point_x ((Znth 0 pts_dedup __default_Point)))) ((point_y ((Znth 0 pts_dedup __default_Point))))) (sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))) ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk ((point_x ((Znth 0 pts_dedup __default_Point)))) ((point_y ((Znth 0 pts_dedup __default_Point))))) (sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))) 1 (unique_n - 1 ) ) ” 
  &&  “ (((Znth 0 (point_swap (pts_dedup_2) (0) (pivot_out)) __default_Point).(x) ) = (point_x ((Znth 0 pts_dedup __default_Point)))) ” 
  &&  “ (((Znth 0 (point_swap (pts_dedup_2) (0) (pivot_out)) __default_Point).(y) ) = (point_y ((Znth 0 pts_dedup __default_Point)))) ”
  &&  (PointArray.full pts_pre unique_n (sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))) )
  **  (PointArray.seg pts_pre unique_n n_pre (sublist (unique_n) (n_pre) ((point_swap (pts_dedup_2) (0) (pivot_out)))) )
).

Definition graham_scan_dedup_entail_wit_2_2 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : ((Zlength (pts_dedup)) = n_pre)) (PreH2 : (pivot_out <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : (points_in_bound pts_l )) (PreH7 : (points_not_all_same pts_l )) (PreH8 : ((Zlength (pts_dedup)) = n_pre)) (PreH9 : (points_in_bound pts_dedup )) (PreH10 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH11 : (0 <= pivot_out)) (PreH12 : (pivot_out < unique_n)) (PreH13 : (unique_n <= n_pre)) (PreH14 : (2 <= unique_n)) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_dedup) (0) (pivot_out)) )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  EX (suffix: (@list Point))  (unique_prefix: (@list Point))  (pts_dedup_2: (@list Point))  (pts_pivot: (@list Point))  (pivot0: Point) ,
  “ (2 <= unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (1 <= (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) < INT_MAX) ” 
  &&  “ (((unique_n - 1 ) + 1 ) <= n_pre) ” 
  &&  “ (pivot0 = (point_mk ((point_x ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point)))))) ” 
  &&  “ (pts_pivot = (point_swap (pts_dedup_2) (0) (pivot_out))) ” 
  &&  “ ((Zlength (pts_dedup_2)) = n_pre) ” 
  &&  “ ((Zlength (pts_pivot)) = n_pre) ” 
  &&  “ ((Zlength (unique_prefix)) = unique_n) ” 
  &&  “ (unique_prefix = (sublist (0) (unique_n) (pts_pivot))) ” 
  &&  “ (suffix = (sublist (unique_n) (n_pre) (pts_pivot))) ” 
  &&  “ (points_in_bound pts_dedup_2 ) ” 
  &&  “ (points_in_bound pts_pivot ) ” 
  &&  “ (points_in_bound unique_prefix ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup_2 unique_n pivot_out ) ” 
  &&  “ (point_no_dup_prefix pts_pivot unique_n ) ” 
  &&  “ (leftmost pivot0 unique_prefix ) ” 
  &&  “ (point_polar_cmp_safe_range pivot0 unique_prefix 1 (unique_n - 1 ) ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = (point_x ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point)))) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = (point_y ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point)))) ”
  &&  (PointArray.full pts_pre unique_n unique_prefix )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_full hull_pre n_pre )
) \/
(
forall (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : ((Zlength (pts_dedup)) = n_pre)) (PreH2 : (pivot_out <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : (points_in_bound pts_l )) (PreH7 : (points_not_all_same pts_l )) (PreH8 : ((Zlength (pts_dedup)) = n_pre)) (PreH9 : (points_in_bound pts_dedup )) (PreH10 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH11 : (0 <= pivot_out)) (PreH12 : (pivot_out < unique_n)) (PreH13 : (unique_n <= n_pre)) (PreH14 : (2 <= unique_n)) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_dedup) (0) (pivot_out)) )
|--
  EX (pts_dedup_2: (@list Point)) ,
  “ (2 <= unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (1 <= (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) < INT_MAX) ” 
  &&  “ (((unique_n - 1 ) + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (pts_dedup_2)) = n_pre) ” 
  &&  “ ((Zlength ((point_swap (pts_dedup_2) (0) (pivot_out)))) = n_pre) ” 
  &&  “ ((Zlength ((sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))))) = unique_n) ” 
  &&  “ (points_in_bound pts_dedup_2 ) ” 
  &&  “ (points_in_bound (point_swap (pts_dedup_2) (0) (pivot_out)) ) ” 
  &&  “ (points_in_bound (sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))) ) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point))))) ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup_2 unique_n pivot_out ) ” 
  &&  “ (point_no_dup_prefix (point_swap (pts_dedup_2) (0) (pivot_out)) unique_n ) ” 
  &&  “ (leftmost (point_mk ((point_x ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point))))) (sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))) ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk ((point_x ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point)))) ((point_y ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point))))) (sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))) 1 (unique_n - 1 ) ) ” 
  &&  “ (((Znth 0 (point_swap (pts_dedup_2) (0) (pivot_out)) __default_Point).(x) ) = (point_x ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point)))) ” 
  &&  “ (((Znth 0 (point_swap (pts_dedup_2) (0) (pivot_out)) __default_Point).(y) ) = (point_y ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point)))) ”
  &&  (PointArray.full pts_pre unique_n (sublist (0) (unique_n) ((point_swap (pts_dedup_2) (0) (pivot_out)))) )
  **  (PointArray.seg pts_pre unique_n n_pre (sublist (unique_n) (n_pre) ((point_swap (pts_dedup_2) (0) (pivot_out)))) )
).

Definition graham_scan_dedup_entail_wit_3 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup_2: (@list Point)) (pts_pivot_2: (@list Point)) (unique_prefix_2: (@list Point)) (suffix_2: (@list Point)) (pivot0_2: Point) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (pts_out: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_out)) = unique_n)) (PreH2 : (points_in_bound pts_out )) (PreH3 : (leftmost (point_mk (gx) (gy)) pts_out )) (PreH4 : (point_permutation unique_prefix_2 pts_out )) (PreH5 : (point_same_outside_range unique_prefix_2 pts_out 1 (unique_n - 1 ) )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx) (gy)) pts_out 1 (unique_n - 1 ) )) (PreH7 : (point_sorted_range (point_mk (gx) (gy)) pts_out 1 (unique_n - 1 ) )) (PreH8 : (2 <= unique_n)) (PreH9 : (unique_n <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (1 <= (unique_n - 1 ))) (PreH12 : ((unique_n - 1 ) < INT_MAX)) (PreH13 : (((unique_n - 1 ) + 1 ) <= n_pre)) (PreH14 : (pivot0_2 = (point_mk (gx) (gy)))) (PreH15 : (pts_pivot_2 = (point_swap (pts_dedup_2) (0) (pivot_idx)))) (PreH16 : ((Zlength (pts_dedup_2)) = n_pre)) (PreH17 : ((Zlength (pts_pivot_2)) = n_pre)) (PreH18 : ((Zlength (unique_prefix_2)) = unique_n)) (PreH19 : (unique_prefix_2 = (sublist (0) (unique_n) (pts_pivot_2)))) (PreH20 : (suffix_2 = (sublist (unique_n) (n_pre) (pts_pivot_2)))) (PreH21 : (points_in_bound pts_dedup_2 )) (PreH22 : (points_in_bound pts_pivot_2 )) (PreH23 : (points_in_bound unique_prefix_2 )) (PreH24 : (point_in_bound pivot0_2 )) (PreH25 : (point_dedup_result pts_l pts_dedup_2 unique_n pivot_idx )) (PreH26 : (point_no_dup_prefix pts_pivot_2 unique_n )) (PreH27 : (leftmost pivot0_2 unique_prefix_2 )) (PreH28 : (point_polar_cmp_safe_range pivot0_2 unique_prefix_2 1 (unique_n - 1 ) )) (PreH29 : (((Znth 0 pts_pivot_2 __default_Point).(x) ) = gx)) (PreH30 : (((Znth 0 pts_pivot_2 __default_Point).(y) ) = gy)) ,
  (PointArray.full pts_pre unique_n pts_out )
  **  (PointArray.seg pts_pre unique_n n_pre suffix_2 )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  EX (suffix: (@list Point))  (tail_sorted: (@list Point))  (unique_prefix: (@list Point))  (pts_sorted: (@list Point))  (pts_dedup: (@list Point))  (pts_pivot: (@list Point))  (pivot0: Point) ,
  “ ((pts_pre + (1 * sizeof( "Point" ))) = (pts_pre + (1 * sizeof( "Point" )))) ” 
  &&  “ (2 <= unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = unique_n) ” 
  &&  “ ((Zlength (unique_prefix)) = unique_n) ” 
  &&  “ ((Zlength (tail_sorted)) = (unique_n - 1 )) ” 
  &&  “ (unique_prefix = (sublist (0) (unique_n) (pts_pivot))) ” 
  &&  “ (tail_sorted = (sublist (1) (unique_n) (pts_sorted))) ” 
  &&  “ (suffix = (sublist (unique_n) (n_pre) (pts_pivot))) ” 
  &&  “ ((unique_n - 1 ) = (Zlength (tail_sorted))) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (points_in_bound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup unique_n pivot_idx ) ” 
  &&  “ (leftmost pivot0 pts_sorted ) ” 
  &&  “ (point_permutation unique_prefix pts_sorted ) ” 
  &&  “ (point_sorted_range (point_mk (gx) (gy)) pts_sorted 1 (unique_n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (leftmost pivot0 (rev (tail_sorted)) ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ”
  &&  (store_point pts_pre pivot0 )
  **  (PointArray.full (pts_pre + (1 * sizeof( "Point" ))) (unique_n - 1 ) tail_sorted )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_seg hull_pre 0 ((unique_n - 1 ) + 1 ) )
  **  (PointArray.undef_seg hull_pre ((unique_n - 1 ) + 1 ) n_pre )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup_2: (@list Point)) (pts_pivot_2: (@list Point)) (unique_prefix_2: (@list Point)) (suffix_2: (@list Point)) (pivot0_2: Point) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (pts_out: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_out)) = unique_n)) (PreH2 : (points_in_bound pts_out )) (PreH3 : (leftmost (point_mk (gx) (gy)) pts_out )) (PreH4 : (point_permutation unique_prefix_2 pts_out )) (PreH5 : (point_same_outside_range unique_prefix_2 pts_out 1 (unique_n - 1 ) )) (PreH6 : (point_polar_cmp_safe_range (point_mk (gx) (gy)) pts_out 1 (unique_n - 1 ) )) (PreH7 : (point_sorted_range (point_mk (gx) (gy)) pts_out 1 (unique_n - 1 ) )) (PreH8 : (2 <= unique_n)) (PreH9 : (unique_n <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (1 <= (unique_n - 1 ))) (PreH12 : ((unique_n - 1 ) < INT_MAX)) (PreH13 : (((unique_n - 1 ) + 1 ) <= n_pre)) (PreH14 : (pivot0_2 = (point_mk (gx) (gy)))) (PreH15 : (pts_pivot_2 = (point_swap (pts_dedup_2) (0) (pivot_idx)))) (PreH16 : ((Zlength (pts_dedup_2)) = n_pre)) (PreH17 : ((Zlength (pts_pivot_2)) = n_pre)) (PreH18 : ((Zlength (unique_prefix_2)) = unique_n)) (PreH19 : (unique_prefix_2 = (sublist (0) (unique_n) (pts_pivot_2)))) (PreH20 : (suffix_2 = (sublist (unique_n) (n_pre) (pts_pivot_2)))) (PreH21 : (points_in_bound pts_dedup_2 )) (PreH22 : (points_in_bound pts_pivot_2 )) (PreH23 : (points_in_bound unique_prefix_2 )) (PreH24 : (point_in_bound pivot0_2 )) (PreH25 : (point_dedup_result pts_l pts_dedup_2 unique_n pivot_idx )) (PreH26 : (point_no_dup_prefix pts_pivot_2 unique_n )) (PreH27 : (leftmost pivot0_2 unique_prefix_2 )) (PreH28 : (point_polar_cmp_safe_range pivot0_2 unique_prefix_2 1 (unique_n - 1 ) )) (PreH29 : (((Znth 0 pts_pivot_2 __default_Point).(x) ) = gx)) (PreH30 : (((Znth 0 pts_pivot_2 __default_Point).(y) ) = gy)) ,
  (PointArray.full pts_pre unique_n pts_out )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  EX (pts_sorted: (@list Point))  (pts_dedup: (@list Point)) ,
  “ (suffix_2 = (sublist (unique_n) (n_pre) ((point_swap (pts_dedup) (0) (pivot_idx))))) ” 
  &&  “ (2 <= unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = unique_n) ” 
  &&  “ ((Zlength ((sublist (0) (unique_n) ((point_swap (pts_dedup) (0) (pivot_idx)))))) = unique_n) ” 
  &&  “ ((Zlength ((sublist (1) (unique_n) (pts_sorted)))) = (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) = (Zlength ((sublist (1) (unique_n) (pts_sorted))))) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (points_in_bound (sublist (1) (unique_n) (pts_sorted)) ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup unique_n pivot_idx ) ” 
  &&  “ (leftmost (point_mk (gx) (gy)) pts_sorted ) ” 
  &&  “ (point_permutation (sublist (0) (unique_n) ((point_swap (pts_dedup) (0) (pivot_idx)))) pts_sorted ) ” 
  &&  “ (point_sorted_range (point_mk (gx) (gy)) pts_sorted 1 (unique_n - 1 ) ) ” 
  &&  “ (point_polar_sorted (point_mk (gx) (gy)) (sublist (1) (unique_n) (pts_sorted)) ) ” 
  &&  “ (leftmost (point_mk (gx) (gy)) (rev ((sublist (1) (unique_n) (pts_sorted)))) ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ”
  &&  (store_point pts_pre (point_mk (gx) (gy)) )
  **  (PointArray.full (pts_pre + (1 * sizeof( "Point" ))) (unique_n - 1 ) (sublist (1) (unique_n) (pts_sorted)) )
  **  (PointArray.undef_seg hull_pre 0 ((unique_n - 1 ) + 1 ) )
  **  (PointArray.undef_seg hull_pre ((unique_n - 1 ) + 1 ) n_pre )
).

Definition graham_scan_dedup_entail_wit_4 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (unique_prefix: (@list Point)) (tail_sorted: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (tail: Z) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (hull_out_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval = (Zlength (hull_out_2)))) (PreH2 : (point_in_bound pivot0 )) (PreH3 : (points_in_bound tail_sorted )) (PreH4 : (is_convex_hull (cons (pivot0) (tail_sorted)) hull_out_2 )) (PreH5 : (tail = (pts_pre + (1 * sizeof( "Point" ))))) (PreH6 : (2 <= unique_n)) (PreH7 : (unique_n <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (pivot0 = (point_mk (gx) (gy)))) (PreH10 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH11 : ((Zlength (pts_dedup)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = unique_n)) (PreH13 : ((Zlength (unique_prefix)) = unique_n)) (PreH14 : ((Zlength (tail_sorted)) = (unique_n - 1 ))) (PreH15 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH16 : (tail_sorted = (sublist (1) (unique_n) (pts_sorted)))) (PreH17 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH18 : ((unique_n - 1 ) = (Zlength (tail_sorted)))) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (points_in_bound tail_sorted )) (PreH21 : (point_in_bound pivot0 )) (PreH22 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH23 : (leftmost pivot0 pts_sorted )) (PreH24 : (point_permutation unique_prefix pts_sorted )) (PreH25 : (point_sorted_range (point_mk (gx) (gy)) pts_sorted 1 (unique_n - 1 ) )) (PreH26 : (point_polar_sorted pivot0 tail_sorted )) (PreH27 : (leftmost pivot0 (rev (tail_sorted)) )) (PreH28 : (((Znth 0 pts_sorted __default_Point).(x) ) = gx)) (PreH29 : (((Znth 0 pts_sorted __default_Point).(y) ) = gy)) ,
  (store_point pts_pre pivot0 )
  **  (PointArray.full tail (unique_n - 1 ) tail_sorted )
  **  (PointArray.seg hull_pre 0 retval hull_out_2 )
  **  (PointArray.undef_seg hull_pre retval ((unique_n - 1 ) + 1 ) )
  **  (PointArray.undef_seg hull_pre ((unique_n - 1 ) + 1 ) n_pre )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
|--
  EX (hull_out: (@list Point))  (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= n_pre) ” 
  &&  “ ((Zlength (hull_out)) = retval) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (is_convex_hull pts_l hull_out ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  (PointArray.seg hull_pre 0 retval hull_out )
  **  (PointArray.undef_seg hull_pre retval n_pre )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (unique_prefix: (@list Point)) (tail_sorted: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (tail: Z) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z) (hull_out_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((point_x (pivot0)) <= INT_MAX)) (PreH2 : ((point_y (pivot0)) <= INT_MAX)) (PreH3 : ((point_x (pivot0)) >= INT_MIN)) (PreH4 : ((point_y (pivot0)) >= INT_MIN)) (PreH5 : (retval = (Zlength (hull_out_2)))) (PreH6 : (point_in_bound pivot0 )) (PreH7 : (points_in_bound tail_sorted )) (PreH8 : (is_convex_hull (cons (pivot0) (tail_sorted)) hull_out_2 )) (PreH9 : (tail = (pts_pre + (1 * sizeof( "Point" ))))) (PreH10 : (2 <= unique_n)) (PreH11 : (unique_n <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : (pivot0 = (point_mk (gx) (gy)))) (PreH14 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH15 : ((Zlength (pts_dedup)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = unique_n)) (PreH17 : ((Zlength (unique_prefix)) = unique_n)) (PreH18 : ((Zlength (tail_sorted)) = (unique_n - 1 ))) (PreH19 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH20 : (tail_sorted = (sublist (1) (unique_n) (pts_sorted)))) (PreH21 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH22 : ((unique_n - 1 ) = (Zlength (tail_sorted)))) (PreH23 : (points_in_bound pts_sorted )) (PreH24 : (points_in_bound tail_sorted )) (PreH25 : (point_in_bound pivot0 )) (PreH26 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH27 : (leftmost pivot0 pts_sorted )) (PreH28 : (point_permutation unique_prefix pts_sorted )) (PreH29 : (point_sorted_range (point_mk (gx) (gy)) pts_sorted 1 (unique_n - 1 ) )) (PreH30 : (point_polar_sorted pivot0 tail_sorted )) (PreH31 : (leftmost pivot0 (rev (tail_sorted)) )) (PreH32 : (((Znth 0 pts_sorted __default_Point).(x) ) = gx)) (PreH33 : (((Znth 0 pts_sorted __default_Point).(y) ) = gy)) ,
  ((&((pts_pre)  # "Point" ->ₛ "y")) # Int  |-> (point_y (pivot0)))
  **  ((&((pts_pre)  # "Point" ->ₛ "x")) # Int  |-> (point_x (pivot0)))
  **  (PointArray.full tail (unique_n - 1 ) tail_sorted )
  **  (PointArray.undef_seg hull_pre retval ((unique_n - 1 ) + 1 ) )
  **  (PointArray.undef_seg hull_pre ((unique_n - 1 ) + 1 ) n_pre )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= n_pre) ” 
  &&  “ ((Zlength (hull_out_2)) = retval) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (is_convex_hull pts_l hull_out_2 ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  (PointArray.undef_seg hull_pre retval n_pre )
).

Definition graham_scan_dedup_return_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (hull_out_2: (@list Point)) (ret: Z) (PreH1 : ((Zlength (pts_out_2)) = n_pre)) (PreH2 : (0 <= ret)) (PreH3 : (ret <= n_pre)) (PreH4 : ((Zlength (hull_out_2)) = ret)) (PreH5 : (points_in_bound pts_out_2 )) (PreH6 : (is_convex_hull pts_l hull_out_2 )) ,
  (PointArray.full pts_pre n_pre pts_out_2 )
  **  (PointArray.seg hull_pre 0 ret hull_out_2 )
  **  (PointArray.undef_seg hull_pre ret n_pre )
|--
  EX (hull_out: (@list Point))  (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (0 <= ret) ” 
  &&  “ (ret <= n_pre) ” 
  &&  “ ((Zlength (hull_out)) = ret) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (is_convex_hull pts_l hull_out ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  (PointArray.seg hull_pre 0 ret hull_out )
  **  (PointArray.undef_seg hull_pre ret n_pre )
.

Definition graham_scan_dedup_partial_solve_wit_1_pure := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) ,
  ((( &( "unique_n" ) )) # Int  |->_)
  **  ((( &( "pivot_idx" ) )) # Int  |-> 0)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (points_in_bound pts_l ) ”
.

Definition graham_scan_dedup_partial_solve_wit_1_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) ,
  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (points_not_all_same pts_l ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre n_pre )
.

Definition graham_scan_dedup_partial_solve_wit_1 := graham_scan_dedup_partial_solve_wit_1_pure -> graham_scan_dedup_partial_solve_wit_1_aux.

Definition graham_scan_dedup_partial_solve_wit_2_pure := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z) (PreH1 : (pivot_out <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : (points_in_bound pts_l )) (PreH6 : (points_not_all_same pts_l )) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : (points_in_bound pts_dedup )) (PreH9 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH10 : (0 <= pivot_out)) (PreH11 : (pivot_out < unique_n)) (PreH12 : (unique_n <= n_pre)) (PreH13 : (2 <= unique_n)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_out)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (0 <= pivot_out) ” 
  &&  “ (pivot_out < n_pre) ” 
  &&  “ (0 <> pivot_out) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ”
.

Definition graham_scan_dedup_partial_solve_wit_2_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z) (PreH1 : (pivot_out <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : (points_in_bound pts_l )) (PreH6 : (points_not_all_same pts_l )) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : (points_in_bound pts_dedup )) (PreH9 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH10 : (0 <= pivot_out)) (PreH11 : (pivot_out < unique_n)) (PreH12 : (unique_n <= n_pre)) (PreH13 : (2 <= unique_n)) ,
  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= 0) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (0 <= pivot_out) ” 
  &&  “ (pivot_out < n_pre) ” 
  &&  “ (0 <> pivot_out) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ (pivot_out <> 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (points_not_all_same pts_l ) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ (points_in_bound pts_dedup ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup unique_n pivot_out ) ” 
  &&  “ (0 <= pivot_out) ” 
  &&  “ (pivot_out < unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (2 <= unique_n) ”
  &&  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
.

Definition graham_scan_dedup_partial_solve_wit_2 := graham_scan_dedup_partial_solve_wit_2_pure -> graham_scan_dedup_partial_solve_wit_2_aux.

Definition graham_scan_dedup_partial_solve_wit_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : ((Zlength (pts_dedup)) = n_pre)) (PreH2 : (pivot_out <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : (points_in_bound pts_l )) (PreH7 : (points_not_all_same pts_l )) (PreH8 : ((Zlength (pts_dedup)) = n_pre)) (PreH9 : (points_in_bound pts_dedup )) (PreH10 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH11 : (0 <= pivot_out)) (PreH12 : (pivot_out < unique_n)) (PreH13 : (unique_n <= n_pre)) (PreH14 : (2 <= unique_n)) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_dedup) (0) (pivot_out)) )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ (pivot_out <> 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (points_not_all_same pts_l ) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ (points_in_bound pts_dedup ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup unique_n pivot_out ) ” 
  &&  “ (0 <= pivot_out) ” 
  &&  “ (pivot_out < unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (2 <= unique_n) ”
  &&  ((&(((pts_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point))))
  **  (PointArray.missing_i pts_pre 0 0 n_pre (point_swap (pts_dedup) (0) (pivot_out)) )
  **  ((&(((pts_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point))))
  **  (PointArray.undef_full hull_pre n_pre )
.

Definition graham_scan_dedup_partial_solve_wit_4 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : (pivot_out = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : (points_in_bound pts_l )) (PreH6 : (points_not_all_same pts_l )) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : (points_in_bound pts_dedup )) (PreH9 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH10 : (0 <= pivot_out)) (PreH11 : (pivot_out < unique_n)) (PreH12 : (unique_n <= n_pre)) (PreH13 : (2 <= unique_n)) ,
  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (pivot_out = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (points_not_all_same pts_l ) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ (points_in_bound pts_dedup ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup unique_n pivot_out ) ” 
  &&  “ (0 <= pivot_out) ” 
  &&  “ (pivot_out < unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (2 <= unique_n) ”
  &&  ((&(((pts_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth 0 pts_dedup __default_Point))))
  **  (PointArray.missing_i pts_pre 0 0 n_pre pts_dedup )
  **  ((&(((pts_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth 0 pts_dedup __default_Point))))
  **  (PointArray.undef_full hull_pre n_pre )
.

Definition graham_scan_dedup_partial_solve_wit_5 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : ((Zlength (pts_dedup)) = n_pre)) (PreH2 : (pivot_out <> 0)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : (points_in_bound pts_l )) (PreH7 : (points_not_all_same pts_l )) (PreH8 : ((Zlength (pts_dedup)) = n_pre)) (PreH9 : (points_in_bound pts_dedup )) (PreH10 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH11 : (0 <= pivot_out)) (PreH12 : (pivot_out < unique_n)) (PreH13 : (unique_n <= n_pre)) (PreH14 : (2 <= unique_n)) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_dedup) (0) (pivot_out)) )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ (pivot_out <> 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (points_not_all_same pts_l ) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ (points_in_bound pts_dedup ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup unique_n pivot_out ) ” 
  &&  “ (0 <= pivot_out) ” 
  &&  “ (pivot_out < unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (2 <= unique_n) ”
  &&  ((&(((pts_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point))))
  **  (PointArray.missing_i pts_pre 0 0 n_pre (point_swap (pts_dedup) (0) (pivot_out)) )
  **  ((&(((pts_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth 0 (point_swap (pts_dedup) (0) (pivot_out)) __default_Point))))
  **  (PointArray.undef_full hull_pre n_pre )
.

Definition graham_scan_dedup_partial_solve_wit_6 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pivot_out: Z) (unique_n: Z)  __default_Point (PreH1 : (pivot_out = 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((Zlength (pts_l)) = n_pre)) (PreH5 : (points_in_bound pts_l )) (PreH6 : (points_not_all_same pts_l )) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : (points_in_bound pts_dedup )) (PreH9 : (point_dedup_result pts_l pts_dedup unique_n pivot_out )) (PreH10 : (0 <= pivot_out)) (PreH11 : (pivot_out < unique_n)) (PreH12 : (unique_n <= n_pre)) (PreH13 : (2 <= unique_n)) ,
  (PointArray.full pts_pre n_pre pts_dedup )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (pivot_out = 0) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (points_not_all_same pts_l ) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ (points_in_bound pts_dedup ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup unique_n pivot_out ) ” 
  &&  “ (0 <= pivot_out) ” 
  &&  “ (pivot_out < unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (2 <= unique_n) ”
  &&  ((&(((pts_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth 0 pts_dedup __default_Point))))
  **  (PointArray.missing_i pts_pre 0 0 n_pre pts_dedup )
  **  ((&(((pts_pre + (0 * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth 0 pts_dedup __default_Point))))
  **  (PointArray.undef_full hull_pre n_pre )
.

Definition graham_scan_dedup_partial_solve_wit_7_pure := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (unique_prefix: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point (PreH1 : (2 <= unique_n)) (PreH2 : (unique_n <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (1 <= (unique_n - 1 ))) (PreH5 : ((unique_n - 1 ) < INT_MAX)) (PreH6 : (((unique_n - 1 ) + 1 ) <= n_pre)) (PreH7 : (pivot0 = (point_mk (gx) (gy)))) (PreH8 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH9 : ((Zlength (pts_dedup)) = n_pre)) (PreH10 : ((Zlength (pts_pivot)) = n_pre)) (PreH11 : ((Zlength (unique_prefix)) = unique_n)) (PreH12 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH13 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH14 : (points_in_bound pts_dedup )) (PreH15 : (points_in_bound pts_pivot )) (PreH16 : (points_in_bound unique_prefix )) (PreH17 : (point_in_bound pivot0 )) (PreH18 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH19 : (point_no_dup_prefix pts_pivot unique_n )) (PreH20 : (leftmost pivot0 unique_prefix )) (PreH21 : (point_polar_cmp_safe_range pivot0 unique_prefix 1 (unique_n - 1 ) )) (PreH22 : (((Znth 0 pts_pivot __default_Point).(x) ) = gx)) (PreH23 : (((Znth 0 pts_pivot __default_Point).(y) ) = gy)) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (PointArray.full pts_pre unique_n unique_prefix )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= 50000) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((-1) <= (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) < unique_n) ” 
  &&  “ ((Zlength (unique_prefix)) = unique_n) ” 
  &&  “ (points_in_bound unique_prefix ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (leftmost (point_mk (gx) (gy)) unique_prefix ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx) (gy)) unique_prefix 1 (unique_n - 1 ) ) ”
.

Definition graham_scan_dedup_partial_solve_wit_7_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (unique_prefix: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point (PreH1 : (2 <= unique_n)) (PreH2 : (unique_n <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (1 <= (unique_n - 1 ))) (PreH5 : ((unique_n - 1 ) < INT_MAX)) (PreH6 : (((unique_n - 1 ) + 1 ) <= n_pre)) (PreH7 : (pivot0 = (point_mk (gx) (gy)))) (PreH8 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH9 : ((Zlength (pts_dedup)) = n_pre)) (PreH10 : ((Zlength (pts_pivot)) = n_pre)) (PreH11 : ((Zlength (unique_prefix)) = unique_n)) (PreH12 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH13 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH14 : (points_in_bound pts_dedup )) (PreH15 : (points_in_bound pts_pivot )) (PreH16 : (points_in_bound unique_prefix )) (PreH17 : (point_in_bound pivot0 )) (PreH18 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH19 : (point_no_dup_prefix pts_pivot unique_n )) (PreH20 : (leftmost pivot0 unique_prefix )) (PreH21 : (point_polar_cmp_safe_range pivot0 unique_prefix 1 (unique_n - 1 ) )) (PreH22 : (((Znth 0 pts_pivot __default_Point).(x) ) = gx)) (PreH23 : (((Znth 0 pts_pivot __default_Point).(y) ) = gy)) ,
  (PointArray.full pts_pre unique_n unique_prefix )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_full hull_pre n_pre )
|--
  “ (0 <= unique_n) ” 
  &&  “ (unique_n <= 50000) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((-1) <= (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) < unique_n) ” 
  &&  “ ((Zlength (unique_prefix)) = unique_n) ” 
  &&  “ (points_in_bound unique_prefix ) ” 
  &&  “ (point_in_bound (point_mk (gx) (gy)) ) ” 
  &&  “ (leftmost (point_mk (gx) (gy)) unique_prefix ) ” 
  &&  “ (point_polar_cmp_safe_range (point_mk (gx) (gy)) unique_prefix 1 (unique_n - 1 ) ) ” 
  &&  “ (2 <= unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (1 <= (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) < INT_MAX) ” 
  &&  “ (((unique_n - 1 ) + 1 ) <= n_pre) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ ((Zlength (pts_pivot)) = n_pre) ” 
  &&  “ ((Zlength (unique_prefix)) = unique_n) ” 
  &&  “ (unique_prefix = (sublist (0) (unique_n) (pts_pivot))) ” 
  &&  “ (suffix = (sublist (unique_n) (n_pre) (pts_pivot))) ” 
  &&  “ (points_in_bound pts_dedup ) ” 
  &&  “ (points_in_bound pts_pivot ) ” 
  &&  “ (points_in_bound unique_prefix ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup unique_n pivot_idx ) ” 
  &&  “ (point_no_dup_prefix pts_pivot unique_n ) ” 
  &&  “ (leftmost pivot0 unique_prefix ) ” 
  &&  “ (point_polar_cmp_safe_range pivot0 unique_prefix 1 (unique_n - 1 ) ) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_pivot __default_Point).(y) ) = gy) ”
  &&  (PointArray.full pts_pre unique_n unique_prefix )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_full hull_pre n_pre )
.

Definition graham_scan_dedup_partial_solve_wit_7 := graham_scan_dedup_partial_solve_wit_7_pure -> graham_scan_dedup_partial_solve_wit_7_aux.

Definition graham_scan_dedup_partial_solve_wit_8_pure := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (unique_prefix: (@list Point)) (tail_sorted: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (tail: Z) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point (PreH1 : (tail = (pts_pre + (1 * sizeof( "Point" ))))) (PreH2 : (2 <= unique_n)) (PreH3 : (unique_n <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (pivot0 = (point_mk (gx) (gy)))) (PreH6 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : ((Zlength (pts_sorted)) = unique_n)) (PreH9 : ((Zlength (unique_prefix)) = unique_n)) (PreH10 : ((Zlength (tail_sorted)) = (unique_n - 1 ))) (PreH11 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH12 : (tail_sorted = (sublist (1) (unique_n) (pts_sorted)))) (PreH13 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH14 : ((unique_n - 1 ) = (Zlength (tail_sorted)))) (PreH15 : (points_in_bound pts_sorted )) (PreH16 : (points_in_bound tail_sorted )) (PreH17 : (point_in_bound pivot0 )) (PreH18 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH19 : (leftmost pivot0 pts_sorted )) (PreH20 : (point_permutation unique_prefix pts_sorted )) (PreH21 : (point_sorted_range (point_mk (gx) (gy)) pts_sorted 1 (unique_n - 1 ) )) (PreH22 : (point_polar_sorted pivot0 tail_sorted )) (PreH23 : (leftmost pivot0 (rev (tail_sorted)) )) (PreH24 : (((Znth 0 pts_sorted __default_Point).(x) ) = gx)) (PreH25 : (((Znth 0 pts_sorted __default_Point).(y) ) = gy)) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "tail" ) )) # Ptr  |-> tail)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "unique_n" ) )) # Int  |-> unique_n)
  **  ((( &( "gy" ) )) # Int  |-> gy)
  **  ((( &( "gx" ) )) # Int  |-> gx)
  **  ((( &( "pivot_idx" ) )) # Int  |-> pivot_idx)
  **  (store_point pts_pre pivot0 )
  **  (PointArray.full tail (unique_n - 1 ) tail_sorted )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_seg hull_pre 0 ((unique_n - 1 ) + 1 ) )
  **  (PointArray.undef_seg hull_pre ((unique_n - 1 ) + 1 ) n_pre )
|--
  “ (1 <= (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) < INT_MAX) ” 
  &&  “ (((unique_n - 1 ) + 1 ) <= n_pre) ” 
  &&  “ ((unique_n - 1 ) = (Zlength (tail_sorted))) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (leftmost pivot0 (rev (tail_sorted)) ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (points_in_bound tail_sorted ) ”
.

Definition graham_scan_dedup_partial_solve_wit_8_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_dedup: (@list Point)) (pts_pivot: (@list Point)) (pts_sorted: (@list Point)) (unique_prefix: (@list Point)) (tail_sorted: (@list Point)) (suffix: (@list Point)) (pivot0: Point) (tail: Z) (unique_n: Z) (gy: Z) (gx: Z) (pivot_idx: Z)  __default_Point (PreH1 : (tail = (pts_pre + (1 * sizeof( "Point" ))))) (PreH2 : (2 <= unique_n)) (PreH3 : (unique_n <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (pivot0 = (point_mk (gx) (gy)))) (PreH6 : (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx)))) (PreH7 : ((Zlength (pts_dedup)) = n_pre)) (PreH8 : ((Zlength (pts_sorted)) = unique_n)) (PreH9 : ((Zlength (unique_prefix)) = unique_n)) (PreH10 : ((Zlength (tail_sorted)) = (unique_n - 1 ))) (PreH11 : (unique_prefix = (sublist (0) (unique_n) (pts_pivot)))) (PreH12 : (tail_sorted = (sublist (1) (unique_n) (pts_sorted)))) (PreH13 : (suffix = (sublist (unique_n) (n_pre) (pts_pivot)))) (PreH14 : ((unique_n - 1 ) = (Zlength (tail_sorted)))) (PreH15 : (points_in_bound pts_sorted )) (PreH16 : (points_in_bound tail_sorted )) (PreH17 : (point_in_bound pivot0 )) (PreH18 : (point_dedup_result pts_l pts_dedup unique_n pivot_idx )) (PreH19 : (leftmost pivot0 pts_sorted )) (PreH20 : (point_permutation unique_prefix pts_sorted )) (PreH21 : (point_sorted_range (point_mk (gx) (gy)) pts_sorted 1 (unique_n - 1 ) )) (PreH22 : (point_polar_sorted pivot0 tail_sorted )) (PreH23 : (leftmost pivot0 (rev (tail_sorted)) )) (PreH24 : (((Znth 0 pts_sorted __default_Point).(x) ) = gx)) (PreH25 : (((Znth 0 pts_sorted __default_Point).(y) ) = gy)) ,
  (store_point pts_pre pivot0 )
  **  (PointArray.full tail (unique_n - 1 ) tail_sorted )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
  **  (PointArray.undef_seg hull_pre 0 ((unique_n - 1 ) + 1 ) )
  **  (PointArray.undef_seg hull_pre ((unique_n - 1 ) + 1 ) n_pre )
|--
  “ (1 <= (unique_n - 1 )) ” 
  &&  “ ((unique_n - 1 ) < INT_MAX) ” 
  &&  “ (((unique_n - 1 ) + 1 ) <= n_pre) ” 
  &&  “ ((unique_n - 1 ) = (Zlength (tail_sorted))) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (leftmost pivot0 (rev (tail_sorted)) ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (points_in_bound tail_sorted ) ” 
  &&  “ (tail = (pts_pre + (1 * sizeof( "Point" )))) ” 
  &&  “ (2 <= unique_n) ” 
  &&  “ (unique_n <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (pivot0 = (point_mk (gx) (gy))) ” 
  &&  “ (pts_pivot = (point_swap (pts_dedup) (0) (pivot_idx))) ” 
  &&  “ ((Zlength (pts_dedup)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = unique_n) ” 
  &&  “ ((Zlength (unique_prefix)) = unique_n) ” 
  &&  “ ((Zlength (tail_sorted)) = (unique_n - 1 )) ” 
  &&  “ (unique_prefix = (sublist (0) (unique_n) (pts_pivot))) ” 
  &&  “ (tail_sorted = (sublist (1) (unique_n) (pts_sorted))) ” 
  &&  “ (suffix = (sublist (unique_n) (n_pre) (pts_pivot))) ” 
  &&  “ ((unique_n - 1 ) = (Zlength (tail_sorted))) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (points_in_bound tail_sorted ) ” 
  &&  “ (point_in_bound pivot0 ) ” 
  &&  “ (point_dedup_result pts_l pts_dedup unique_n pivot_idx ) ” 
  &&  “ (leftmost pivot0 pts_sorted ) ” 
  &&  “ (point_permutation unique_prefix pts_sorted ) ” 
  &&  “ (point_sorted_range (point_mk (gx) (gy)) pts_sorted 1 (unique_n - 1 ) ) ” 
  &&  “ (point_polar_sorted pivot0 tail_sorted ) ” 
  &&  “ (leftmost pivot0 (rev (tail_sorted)) ) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(x) ) = gx) ” 
  &&  “ (((Znth 0 pts_sorted __default_Point).(y) ) = gy) ”
  &&  (store_point pts_pre pivot0 )
  **  (PointArray.full tail (unique_n - 1 ) tail_sorted )
  **  (PointArray.undef_seg hull_pre 0 ((unique_n - 1 ) + 1 ) )
  **  (PointArray.undef_seg hull_pre ((unique_n - 1 ) + 1 ) n_pre )
  **  (PointArray.seg pts_pre unique_n n_pre suffix )
.

Definition graham_scan_dedup_partial_solve_wit_8 := graham_scan_dedup_partial_solve_wit_8_pure -> graham_scan_dedup_partial_solve_wit_8_aux.

Definition build_hull_from_sorted_tail_dedup_derive_high_level_spec_by_low_level_spec := 
forall (hull_pre: Z) (tail_n_pre: Z) (sorted_tail_pre: Z) (pivot_pre: Z) (n_full_high_level_spec: Z) (l_high_level_spec: (@list Point)) (pivot0_high_level_spec: Point) ,
  “ (1 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_high_level_spec) ” 
  &&  “ (tail_n_pre = (Zlength (l_high_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_high_level_spec l_high_level_spec ) ” 
  &&  “ (leftmost pivot0_high_level_spec (rev (l_high_level_spec)) ) ” 
  &&  “ (point_in_bound pivot0_high_level_spec ) ” 
  &&  “ (points_in_bound l_high_level_spec ) ”
  &&  (store_point pivot_pre pivot0_high_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_high_level_spec )
  **  (PointArray.undef_seg hull_pre 0 (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_high_level_spec )
|--
EX (pivot0_low_level_spec: Point) (l_low_level_spec: (@list Point)) (n_full_low_level_spec: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) ,
  (“ (1 <= tail_n_pre) ” 
  &&  “ (tail_n_pre < INT_MAX) ” 
  &&  “ ((tail_n_pre + 1 ) <= n_full_low_level_spec) ” 
  &&  “ (tail_n_pre = (Zlength (l_low_level_spec))) ” 
  &&  “ (point_polar_sorted pivot0_low_level_spec l_low_level_spec ) ” 
  &&  “ (leftmost pivot0_low_level_spec (rev (l_low_level_spec)) ) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (build_hull (pivot0_low_level_spec) (l_low_level_spec)) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.undef_seg hull_pre 0 (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec ))
  **
  ((EX stk retval_2,
  “ (retval_2 = (Zlength ((rev (stk))))) ” 
  &&  “ (point_in_bound pivot0_low_level_spec ) ” 
  &&  “ (points_in_bound l_low_level_spec ) ” 
  &&  “ (points_in_bound (rev (stk)) ) ” 
  &&  “ (safeExec (equiv (stk)) (return (tt)) X_low_level_spec ) ”
  &&  (store_point pivot_pre pivot0_low_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_low_level_spec )
  **  (PointArray.seg hull_pre 0 retval_2 (rev (stk)) )
  **  (PointArray.undef_seg hull_pre retval_2 (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_low_level_spec ))
  -*
  (EX hull_out retval,
  “ (retval = (Zlength (hull_out))) ” 
  &&  “ (point_in_bound pivot0_high_level_spec ) ” 
  &&  “ (points_in_bound l_high_level_spec ) ” 
  &&  “ (is_convex_hull (cons (pivot0_high_level_spec) (l_high_level_spec)) hull_out ) ”
  &&  (store_point pivot_pre pivot0_high_level_spec )
  **  (PointArray.full sorted_tail_pre tail_n_pre l_high_level_spec )
  **  (PointArray.seg hull_pre 0 retval hull_out )
  **  (PointArray.undef_seg hull_pre retval (tail_n_pre + 1 ) )
  **  (PointArray.undef_seg hull_pre (tail_n_pre + 1 ) n_full_high_level_spec )))
.

Module Type VC_Correct.

Include point_array_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_leftdown_dedup_safety_wit_1 : leftdown_dedup_safety_wit_1.
Axiom proof_of_leftdown_dedup_safety_wit_2 : leftdown_dedup_safety_wit_2.
Axiom proof_of_leftdown_dedup_safety_wit_3 : leftdown_dedup_safety_wit_3.
Axiom proof_of_leftdown_dedup_safety_wit_4 : leftdown_dedup_safety_wit_4.
Axiom proof_of_leftdown_dedup_safety_wit_5 : leftdown_dedup_safety_wit_5.
Axiom proof_of_leftdown_dedup_safety_wit_6 : leftdown_dedup_safety_wit_6.
Axiom proof_of_leftdown_dedup_safety_wit_7 : leftdown_dedup_safety_wit_7.
Axiom proof_of_leftdown_dedup_entail_wit_1 : leftdown_dedup_entail_wit_1.
Axiom proof_of_leftdown_dedup_return_wit_1 : leftdown_dedup_return_wit_1.
Axiom proof_of_leftdown_dedup_return_wit_2 : leftdown_dedup_return_wit_2.
Axiom proof_of_leftdown_dedup_return_wit_3 : leftdown_dedup_return_wit_3.
Axiom proof_of_leftdown_dedup_return_wit_4 : leftdown_dedup_return_wit_4.
Axiom proof_of_leftdown_dedup_return_wit_5 : leftdown_dedup_return_wit_5.
Axiom proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Axiom proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Axiom proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Axiom proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Axiom proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Axiom proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Axiom proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Axiom proof_of_cross_prod_entail_wit_1 : cross_prod_entail_wit_1.
Axiom proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Axiom proof_of_dot_prod_safety_wit_1 : dot_prod_safety_wit_1.
Axiom proof_of_dot_prod_safety_wit_2 : dot_prod_safety_wit_2.
Axiom proof_of_dot_prod_safety_wit_3 : dot_prod_safety_wit_3.
Axiom proof_of_dot_prod_safety_wit_4 : dot_prod_safety_wit_4.
Axiom proof_of_dot_prod_safety_wit_5 : dot_prod_safety_wit_5.
Axiom proof_of_dot_prod_safety_wit_6 : dot_prod_safety_wit_6.
Axiom proof_of_dot_prod_safety_wit_7 : dot_prod_safety_wit_7.
Axiom proof_of_dot_prod_entail_wit_1 : dot_prod_entail_wit_1.
Axiom proof_of_dot_prod_return_wit_1 : dot_prod_return_wit_1.
Axiom proof_of_cmp_polar_safety_wit_1 : cmp_polar_safety_wit_1.
Axiom proof_of_cmp_polar_safety_wit_2 : cmp_polar_safety_wit_2.
Axiom proof_of_cmp_polar_safety_wit_3 : cmp_polar_safety_wit_3.
Axiom proof_of_cmp_polar_safety_wit_4 : cmp_polar_safety_wit_4.
Axiom proof_of_cmp_polar_safety_wit_5 : cmp_polar_safety_wit_5.
Axiom proof_of_cmp_polar_safety_wit_6 : cmp_polar_safety_wit_6.
Axiom proof_of_cmp_polar_safety_wit_7 : cmp_polar_safety_wit_7.
Axiom proof_of_cmp_polar_safety_wit_8 : cmp_polar_safety_wit_8.
Axiom proof_of_cmp_polar_safety_wit_9 : cmp_polar_safety_wit_9.
Axiom proof_of_cmp_polar_safety_wit_10 : cmp_polar_safety_wit_10.
Axiom proof_of_cmp_polar_safety_wit_11 : cmp_polar_safety_wit_11.
Axiom proof_of_cmp_polar_entail_wit_1 : cmp_polar_entail_wit_1.
Axiom proof_of_cmp_polar_entail_wit_2 : cmp_polar_entail_wit_2.
Axiom proof_of_cmp_polar_entail_wit_3 : cmp_polar_entail_wit_3.
Axiom proof_of_cmp_polar_return_wit_1 : cmp_polar_return_wit_1.
Axiom proof_of_cmp_polar_return_wit_2 : cmp_polar_return_wit_2.
Axiom proof_of_cmp_polar_return_wit_3 : cmp_polar_return_wit_3.
Axiom proof_of_cmp_polar_return_wit_4 : cmp_polar_return_wit_4.
Axiom proof_of_cmp_polar_return_wit_5 : cmp_polar_return_wit_5.
Axiom proof_of_cmp_polar_partial_solve_wit_1_pure : cmp_polar_partial_solve_wit_1_pure.
Axiom proof_of_cmp_polar_partial_solve_wit_1 : cmp_polar_partial_solve_wit_1.
Axiom proof_of_cmp_polar_partial_solve_wit_2_pure : cmp_polar_partial_solve_wit_2_pure.
Axiom proof_of_cmp_polar_partial_solve_wit_2 : cmp_polar_partial_solve_wit_2.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_1 : build_hull_from_sorted_tail_dedup_safety_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_2 : build_hull_from_sorted_tail_dedup_safety_wit_2.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_3 : build_hull_from_sorted_tail_dedup_safety_wit_3.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_4 : build_hull_from_sorted_tail_dedup_safety_wit_4.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_5 : build_hull_from_sorted_tail_dedup_safety_wit_5.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_6 : build_hull_from_sorted_tail_dedup_safety_wit_6.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_7 : build_hull_from_sorted_tail_dedup_safety_wit_7.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_8 : build_hull_from_sorted_tail_dedup_safety_wit_8.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_9 : build_hull_from_sorted_tail_dedup_safety_wit_9.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_10 : build_hull_from_sorted_tail_dedup_safety_wit_10.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_11 : build_hull_from_sorted_tail_dedup_safety_wit_11.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_12 : build_hull_from_sorted_tail_dedup_safety_wit_12.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_13 : build_hull_from_sorted_tail_dedup_safety_wit_13.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_14 : build_hull_from_sorted_tail_dedup_safety_wit_14.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_15 : build_hull_from_sorted_tail_dedup_safety_wit_15.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_16 : build_hull_from_sorted_tail_dedup_safety_wit_16.
Axiom proof_of_build_hull_from_sorted_tail_dedup_safety_wit_17 : build_hull_from_sorted_tail_dedup_safety_wit_17.
Axiom proof_of_build_hull_from_sorted_tail_dedup_entail_wit_1 : build_hull_from_sorted_tail_dedup_entail_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_dedup_entail_wit_2 : build_hull_from_sorted_tail_dedup_entail_wit_2.
Axiom proof_of_build_hull_from_sorted_tail_dedup_entail_wit_3 : build_hull_from_sorted_tail_dedup_entail_wit_3.
Axiom proof_of_build_hull_from_sorted_tail_dedup_entail_wit_4_1 : build_hull_from_sorted_tail_dedup_entail_wit_4_1.
Axiom proof_of_build_hull_from_sorted_tail_dedup_entail_wit_4_2 : build_hull_from_sorted_tail_dedup_entail_wit_4_2.
Axiom proof_of_build_hull_from_sorted_tail_dedup_return_wit_1 : build_hull_from_sorted_tail_dedup_return_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_1 : build_hull_from_sorted_tail_dedup_partial_solve_wit_1.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_2 : build_hull_from_sorted_tail_dedup_partial_solve_wit_2.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_3 : build_hull_from_sorted_tail_dedup_partial_solve_wit_3.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_4 : build_hull_from_sorted_tail_dedup_partial_solve_wit_4.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_5 : build_hull_from_sorted_tail_dedup_partial_solve_wit_5.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_6 : build_hull_from_sorted_tail_dedup_partial_solve_wit_6.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_7 : build_hull_from_sorted_tail_dedup_partial_solve_wit_7.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_8 : build_hull_from_sorted_tail_dedup_partial_solve_wit_8.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure : build_hull_from_sorted_tail_dedup_partial_solve_wit_9_pure.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_9 : build_hull_from_sorted_tail_dedup_partial_solve_wit_9.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_10 : build_hull_from_sorted_tail_dedup_partial_solve_wit_10.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_11 : build_hull_from_sorted_tail_dedup_partial_solve_wit_11.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_12 : build_hull_from_sorted_tail_dedup_partial_solve_wit_12.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_13 : build_hull_from_sorted_tail_dedup_partial_solve_wit_13.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_14 : build_hull_from_sorted_tail_dedup_partial_solve_wit_14.
Axiom proof_of_build_hull_from_sorted_tail_dedup_partial_solve_wit_15 : build_hull_from_sorted_tail_dedup_partial_solve_wit_15.
Axiom proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Axiom proof_of_swap_points_partial_solve_wit_1 : swap_points_partial_solve_wit_1.
Axiom proof_of_swap_points_partial_solve_wit_2 : swap_points_partial_solve_wit_2.
Axiom proof_of_swap_points_partial_solve_wit_3 : swap_points_partial_solve_wit_3.
Axiom proof_of_swap_points_partial_solve_wit_4 : swap_points_partial_solve_wit_4.
Axiom proof_of_swap_points_partial_solve_wit_5 : swap_points_partial_solve_wit_5.
Axiom proof_of_swap_points_partial_solve_wit_6 : swap_points_partial_solve_wit_6.
Axiom proof_of_swap_points_partial_solve_wit_7 : swap_points_partial_solve_wit_7.
Axiom proof_of_swap_points_partial_solve_wit_8 : swap_points_partial_solve_wit_8.
Axiom proof_of_partition_polar_points_safety_wit_1 : partition_polar_points_safety_wit_1.
Axiom proof_of_partition_polar_points_safety_wit_2 : partition_polar_points_safety_wit_2.
Axiom proof_of_partition_polar_points_safety_wit_3 : partition_polar_points_safety_wit_3.
Axiom proof_of_partition_polar_points_safety_wit_4 : partition_polar_points_safety_wit_4.
Axiom proof_of_partition_polar_points_safety_wit_5 : partition_polar_points_safety_wit_5.
Axiom proof_of_partition_polar_points_safety_wit_6 : partition_polar_points_safety_wit_6.
Axiom proof_of_partition_polar_points_safety_wit_7 : partition_polar_points_safety_wit_7.
Axiom proof_of_partition_polar_points_safety_wit_8 : partition_polar_points_safety_wit_8.
Axiom proof_of_partition_polar_points_safety_wit_9 : partition_polar_points_safety_wit_9.
Axiom proof_of_partition_polar_points_safety_wit_10 : partition_polar_points_safety_wit_10.
Axiom proof_of_partition_polar_points_safety_wit_11 : partition_polar_points_safety_wit_11.
Axiom proof_of_partition_polar_points_safety_wit_12 : partition_polar_points_safety_wit_12.
Axiom proof_of_partition_polar_points_safety_wit_13 : partition_polar_points_safety_wit_13.
Axiom proof_of_partition_polar_points_safety_wit_14 : partition_polar_points_safety_wit_14.
Axiom proof_of_partition_polar_points_safety_wit_15 : partition_polar_points_safety_wit_15.
Axiom proof_of_partition_polar_points_entail_wit_1 : partition_polar_points_entail_wit_1.
Axiom proof_of_partition_polar_points_entail_wit_2_1 : partition_polar_points_entail_wit_2_1.
Axiom proof_of_partition_polar_points_entail_wit_2_2 : partition_polar_points_entail_wit_2_2.
Axiom proof_of_partition_polar_points_entail_wit_2_3 : partition_polar_points_entail_wit_2_3.
Axiom proof_of_partition_polar_points_return_wit_1 : partition_polar_points_return_wit_1.
Axiom proof_of_partition_polar_points_return_wit_2 : partition_polar_points_return_wit_2.
Axiom proof_of_partition_polar_points_partial_solve_wit_1 : partition_polar_points_partial_solve_wit_1.
Axiom proof_of_partition_polar_points_partial_solve_wit_2 : partition_polar_points_partial_solve_wit_2.
Axiom proof_of_partition_polar_points_partial_solve_wit_3 : partition_polar_points_partial_solve_wit_3.
Axiom proof_of_partition_polar_points_partial_solve_wit_4 : partition_polar_points_partial_solve_wit_4.
Axiom proof_of_partition_polar_points_partial_solve_wit_5_pure : partition_polar_points_partial_solve_wit_5_pure.
Axiom proof_of_partition_polar_points_partial_solve_wit_5 : partition_polar_points_partial_solve_wit_5.
Axiom proof_of_partition_polar_points_partial_solve_wit_6_pure : partition_polar_points_partial_solve_wit_6_pure.
Axiom proof_of_partition_polar_points_partial_solve_wit_6 : partition_polar_points_partial_solve_wit_6.
Axiom proof_of_partition_polar_points_partial_solve_wit_7_pure : partition_polar_points_partial_solve_wit_7_pure.
Axiom proof_of_partition_polar_points_partial_solve_wit_7 : partition_polar_points_partial_solve_wit_7.
Axiom proof_of_quicksort_polar_points_safety_wit_1 : quicksort_polar_points_safety_wit_1.
Axiom proof_of_quicksort_polar_points_safety_wit_2 : quicksort_polar_points_safety_wit_2.
Axiom proof_of_quicksort_polar_points_safety_wit_3 : quicksort_polar_points_safety_wit_3.
Axiom proof_of_quicksort_polar_points_safety_wit_4 : quicksort_polar_points_safety_wit_4.
Axiom proof_of_quicksort_polar_points_safety_wit_5 : quicksort_polar_points_safety_wit_5.
Axiom proof_of_quicksort_polar_points_safety_wit_6 : quicksort_polar_points_safety_wit_6.
Axiom proof_of_quicksort_polar_points_safety_wit_7 : quicksort_polar_points_safety_wit_7.
Axiom proof_of_quicksort_polar_points_return_wit_1 : quicksort_polar_points_return_wit_1.
Axiom proof_of_quicksort_polar_points_return_wit_2 : quicksort_polar_points_return_wit_2.
Axiom proof_of_quicksort_polar_points_return_wit_3 : quicksort_polar_points_return_wit_3.
Axiom proof_of_quicksort_polar_points_return_wit_4 : quicksort_polar_points_return_wit_4.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_1_pure : quicksort_polar_points_partial_solve_wit_1_pure.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_1 : quicksort_polar_points_partial_solve_wit_1.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_2_pure : quicksort_polar_points_partial_solve_wit_2_pure.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_2 : quicksort_polar_points_partial_solve_wit_2.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_3_pure : quicksort_polar_points_partial_solve_wit_3_pure.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_3 : quicksort_polar_points_partial_solve_wit_3.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_4_pure : quicksort_polar_points_partial_solve_wit_4_pure.
Axiom proof_of_quicksort_polar_points_partial_solve_wit_4 : quicksort_polar_points_partial_solve_wit_4.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_1 : dedup_points_and_find_leftmost_safety_wit_1.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_2 : dedup_points_and_find_leftmost_safety_wit_2.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_3 : dedup_points_and_find_leftmost_safety_wit_3.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_4 : dedup_points_and_find_leftmost_safety_wit_4.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_5 : dedup_points_and_find_leftmost_safety_wit_5.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_6 : dedup_points_and_find_leftmost_safety_wit_6.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_7 : dedup_points_and_find_leftmost_safety_wit_7.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_8 : dedup_points_and_find_leftmost_safety_wit_8.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_9 : dedup_points_and_find_leftmost_safety_wit_9.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_10 : dedup_points_and_find_leftmost_safety_wit_10.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_11 : dedup_points_and_find_leftmost_safety_wit_11.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_12 : dedup_points_and_find_leftmost_safety_wit_12.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_13 : dedup_points_and_find_leftmost_safety_wit_13.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_14 : dedup_points_and_find_leftmost_safety_wit_14.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_15 : dedup_points_and_find_leftmost_safety_wit_15.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_16 : dedup_points_and_find_leftmost_safety_wit_16.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_17 : dedup_points_and_find_leftmost_safety_wit_17.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_18 : dedup_points_and_find_leftmost_safety_wit_18.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_19 : dedup_points_and_find_leftmost_safety_wit_19.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_20 : dedup_points_and_find_leftmost_safety_wit_20.
Axiom proof_of_dedup_points_and_find_leftmost_safety_wit_21 : dedup_points_and_find_leftmost_safety_wit_21.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_1 : dedup_points_and_find_leftmost_entail_wit_1.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_2 : dedup_points_and_find_leftmost_entail_wit_2.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_3_1 : dedup_points_and_find_leftmost_entail_wit_3_1.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_3_2 : dedup_points_and_find_leftmost_entail_wit_3_2.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_4_1 : dedup_points_and_find_leftmost_entail_wit_4_1.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_4_2 : dedup_points_and_find_leftmost_entail_wit_4_2.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_5_1 : dedup_points_and_find_leftmost_entail_wit_5_1.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_5_2 : dedup_points_and_find_leftmost_entail_wit_5_2.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_5_3 : dedup_points_and_find_leftmost_entail_wit_5_3.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_5_4 : dedup_points_and_find_leftmost_entail_wit_5_4.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_5_5 : dedup_points_and_find_leftmost_entail_wit_5_5.
Axiom proof_of_dedup_points_and_find_leftmost_entail_wit_5_6 : dedup_points_and_find_leftmost_entail_wit_5_6.
Axiom proof_of_dedup_points_and_find_leftmost_return_wit_1 : dedup_points_and_find_leftmost_return_wit_1.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_1 : dedup_points_and_find_leftmost_partial_solve_wit_1.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_2 : dedup_points_and_find_leftmost_partial_solve_wit_2.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_3 : dedup_points_and_find_leftmost_partial_solve_wit_3.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_4 : dedup_points_and_find_leftmost_partial_solve_wit_4.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_5_pure : dedup_points_and_find_leftmost_partial_solve_wit_5_pure.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_5 : dedup_points_and_find_leftmost_partial_solve_wit_5.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_6 : dedup_points_and_find_leftmost_partial_solve_wit_6.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_7 : dedup_points_and_find_leftmost_partial_solve_wit_7.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_8 : dedup_points_and_find_leftmost_partial_solve_wit_8.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_9 : dedup_points_and_find_leftmost_partial_solve_wit_9.
Axiom proof_of_dedup_points_and_find_leftmost_partial_solve_wit_10 : dedup_points_and_find_leftmost_partial_solve_wit_10.
Axiom proof_of_graham_scan_dedup_safety_wit_1 : graham_scan_dedup_safety_wit_1.
Axiom proof_of_graham_scan_dedup_safety_wit_2 : graham_scan_dedup_safety_wit_2.
Axiom proof_of_graham_scan_dedup_safety_wit_3 : graham_scan_dedup_safety_wit_3.
Axiom proof_of_graham_scan_dedup_safety_wit_4 : graham_scan_dedup_safety_wit_4.
Axiom proof_of_graham_scan_dedup_safety_wit_5 : graham_scan_dedup_safety_wit_5.
Axiom proof_of_graham_scan_dedup_safety_wit_6 : graham_scan_dedup_safety_wit_6.
Axiom proof_of_graham_scan_dedup_safety_wit_7 : graham_scan_dedup_safety_wit_7.
Axiom proof_of_graham_scan_dedup_safety_wit_8 : graham_scan_dedup_safety_wit_8.
Axiom proof_of_graham_scan_dedup_safety_wit_9 : graham_scan_dedup_safety_wit_9.
Axiom proof_of_graham_scan_dedup_safety_wit_10 : graham_scan_dedup_safety_wit_10.
Axiom proof_of_graham_scan_dedup_safety_wit_11 : graham_scan_dedup_safety_wit_11.
Axiom proof_of_graham_scan_dedup_safety_wit_12 : graham_scan_dedup_safety_wit_12.
Axiom proof_of_graham_scan_dedup_safety_wit_13 : graham_scan_dedup_safety_wit_13.
Axiom proof_of_graham_scan_dedup_safety_wit_14 : graham_scan_dedup_safety_wit_14.
Axiom proof_of_graham_scan_dedup_safety_wit_15 : graham_scan_dedup_safety_wit_15.
Axiom proof_of_graham_scan_dedup_entail_wit_1 : graham_scan_dedup_entail_wit_1.
Axiom proof_of_graham_scan_dedup_entail_wit_2_1 : graham_scan_dedup_entail_wit_2_1.
Axiom proof_of_graham_scan_dedup_entail_wit_2_2 : graham_scan_dedup_entail_wit_2_2.
Axiom proof_of_graham_scan_dedup_entail_wit_3 : graham_scan_dedup_entail_wit_3.
Axiom proof_of_graham_scan_dedup_entail_wit_4 : graham_scan_dedup_entail_wit_4.
Axiom proof_of_graham_scan_dedup_return_wit_1 : graham_scan_dedup_return_wit_1.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_1_pure : graham_scan_dedup_partial_solve_wit_1_pure.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_1 : graham_scan_dedup_partial_solve_wit_1.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_2_pure : graham_scan_dedup_partial_solve_wit_2_pure.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_2 : graham_scan_dedup_partial_solve_wit_2.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_3 : graham_scan_dedup_partial_solve_wit_3.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_4 : graham_scan_dedup_partial_solve_wit_4.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_5 : graham_scan_dedup_partial_solve_wit_5.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_6 : graham_scan_dedup_partial_solve_wit_6.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_7_pure : graham_scan_dedup_partial_solve_wit_7_pure.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_7 : graham_scan_dedup_partial_solve_wit_7.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_8_pure : graham_scan_dedup_partial_solve_wit_8_pure.
Axiom proof_of_graham_scan_dedup_partial_solve_wit_8 : graham_scan_dedup_partial_solve_wit_8.
Axiom proof_of_build_hull_from_sorted_tail_dedup_derive_high_level_spec_by_low_level_spec : build_hull_from_sorted_tail_dedup_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
