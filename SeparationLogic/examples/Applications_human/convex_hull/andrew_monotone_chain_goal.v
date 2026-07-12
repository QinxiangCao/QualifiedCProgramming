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

(*----- Function cmp_xy -----*)

Definition cmp_xy_safety_wit_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre < b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_xy_safety_wit_2 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre < b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_xy_safety_wit_3 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_xy_safety_wit_4 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition cmp_xy_safety_wit_5 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_xy_safety_wit_6 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition cmp_xy_safety_wit_7 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  ((( &( "a_x" ) )) # Int  |-> a_x_pre)
  **  ((( &( "a_y" ) )) # Int  |-> a_y_pre)
  **  ((( &( "b_x" ) )) # Int  |-> b_x_pre)
  **  ((( &( "b_y" ) )) # Int  |-> b_y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition cmp_xy_entail_wit_1 := 
  TT && emp 
|--
  TT && emp 
.

Definition cmp_xy_return_wit_1 := 
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

Definition cmp_xy_return_wit_1_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  (0 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_xy_return_wit_2 := 
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

Definition cmp_xy_return_wit_2_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) ,
  (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_xy_return_wit_3 := 
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

Definition cmp_xy_return_wit_3_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) ,
  ((-1) = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_xy_return_wit_4 := 
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

Definition cmp_xy_return_wit_4_split_goal_1 := 
forall (b_y_pre: Z) (b_x_pre: Z) (a_y_pre: Z) (a_x_pre: Z) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) ,
  (1 = (point_cmp_leftdown ((point_mk (a_x_pre) (a_y_pre))) ((point_mk (b_x_pre) (b_y_pre)))))
.

Definition cmp_xy_return_wit_5 := 
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

Definition cmp_xy_return_wit_5_split_goal_1 := 
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

(*----- Function partition_xy_points -----*)

Definition partition_xy_points_safety_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  ((( &( "pivot_y" ) )) # Int  |-> (point_y ((Znth high_pre pts_l __default_Point))))
  **  ((( &( "pivot_x" ) )) # Int  |-> (point_x ((Znth high_pre pts_l __default_Point))))
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((low_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low_pre - 1 )) ”
.

Definition partition_xy_points_safety_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  ((( &( "pivot_y" ) )) # Int  |-> (point_y ((Znth high_pre pts_l __default_Point))))
  **  ((( &( "pivot_x" ) )) # Int  |-> (point_x ((Znth high_pre pts_l __default_Point))))
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_xy_points_safety_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH2 : (j < high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |-> retval)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition partition_xy_points_safety_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |-> retval)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_xy_points_safety_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (j)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_xy_points_safety_wit_6 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_xy_points_safety_wit_7 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_xy_points_safety_wit_8 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j >= high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH15 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Int  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Int  |-> pivot_y)
  **  (PointArray.full pts_pre n_pre pts_cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_xy_points_entail_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
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
  &&  “ (point_in_bound (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) ) ” 
  &&  “ (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) (low_pre - 1 ) low_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
  TT && emp 
|--
  “ (point_xy_partition_scan_inv pts_l pts_l low_pre high_pre (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) (low_pre - 1 ) low_pre ) ” 
  &&  “ (point_in_bound (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) ) ” 
  &&  “ (((Znth high_pre pts_l __default_Point).(y) ) = (point_y ((Znth high_pre pts_l __default_Point)))) ” 
  &&  “ (((Znth high_pre pts_l __default_Point).(x) ) = (point_x ((Znth high_pre pts_l __default_Point)))) ”
  &&  emp
).

Definition partition_xy_points_entail_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
  (point_xy_partition_scan_inv pts_l pts_l low_pre high_pre (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) (low_pre - 1 ) low_pre )
.

Definition partition_xy_points_entail_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
  (point_in_bound (point_mk ((point_x ((Znth high_pre pts_l __default_Point)))) ((point_y ((Znth high_pre pts_l __default_Point))))) )
.

Definition partition_xy_points_entail_wit_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
  (((Znth high_pre pts_l __default_Point).(y) ) = (point_y ((Znth high_pre pts_l __default_Point))))
.

Definition partition_xy_points_entail_wit_1_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
  (((Znth high_pre pts_l __default_Point).(x) ) = (point_x ((Znth high_pre pts_l __default_Point))))
.

Definition partition_xy_points_entail_wit_2_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
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
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_xy_partition_scan_inv pts_l (point_swap (pts_cur_2) ((i + 1 )) (j)) low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ” 
  &&  “ (points_in_bound (point_swap (pts_cur_2) ((i + 1 )) (j)) ) ” 
  &&  “ (((Znth high_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) __default_Point).(y) ) = pivot_y) ” 
  &&  “ (((Znth high_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) __default_Point).(x) ) = pivot_x) ” 
  &&  “ ((Zlength ((point_swap (pts_cur_2) ((i + 1 )) (j)))) = n_pre) ”
  &&  emp
).

Definition partition_xy_points_entail_wit_2_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_xy_partition_scan_inv pts_l (point_swap (pts_cur_2) ((i + 1 )) (j)) low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) )
.

Definition partition_xy_points_entail_wit_2_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (points_in_bound (point_swap (pts_cur_2) ((i + 1 )) (j)) )
.

Definition partition_xy_points_entail_wit_2_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (((Znth high_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) __default_Point).(y) ) = pivot_y)
.

Definition partition_xy_points_entail_wit_2_1_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (((Znth high_pre (point_swap (pts_cur_2) ((i + 1 )) (j)) __default_Point).(x) ) = pivot_x)
.

Definition partition_xy_points_entail_wit_2_1_split_goal_5 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((Zlength (pts_cur_2)) = n_pre)) (PreH2 : ((i + 1 ) <> j)) (PreH3 : (retval <= 0)) (PreH4 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH5 : (j < high_pre)) (PreH6 : ((Zlength (pts_cur_2)) = n_pre)) (PreH7 : (0 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre <= high_pre)) (PreH11 : (high_pre < n_pre)) (PreH12 : ((low_pre - 1 ) <= i)) (PreH13 : (i < j)) (PreH14 : (j <= high_pre)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH16 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH17 : (points_in_bound pts_cur_2 )) (PreH18 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH19 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((Zlength ((point_swap (pts_cur_2) ((i + 1 )) (j)))) = n_pre)
.

Definition partition_xy_points_entail_wit_2_2 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
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
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  emp
).

Definition partition_xy_points_entail_wit_2_2_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur_2)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur_2 )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) )
.

Definition partition_xy_points_entail_wit_2_3 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur_2)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
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
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i (j + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur_2)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i (j + 1 ) ) ”
  &&  emp
).

Definition partition_xy_points_entail_wit_2_3_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur_2: (@list Point)) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur_2 __default_Point)))) ((point_y ((Znth j pts_cur_2 __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : ((Zlength (pts_cur_2)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur_2 __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur_2 __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur_2 )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_xy_partition_scan_inv pts_l pts_cur_2 low_pre high_pre (point_mk (pivot_x) (pivot_y)) i (j + 1 ) )
.

Definition partition_xy_points_return_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
|--
  EX (pts_out: (@list Point)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out low_pre high_pre ) ” 
  &&  “ (point_xy_partitioned_at pts_out low_pre high_pre (i + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_xy_partitioned_at (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre (i + 1 ) ) ” 
  &&  “ (point_same_outside_range pts_l (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre ) ” 
  &&  “ (point_permutation pts_l (point_swap (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ (points_in_bound (point_swap (pts_cur) ((i + 1 )) (high_pre)) ) ” 
  &&  “ ((Zlength ((point_swap (pts_cur) ((i + 1 )) (high_pre)))) = n_pre) ”
  &&  emp
).

Definition partition_xy_points_return_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_xy_partitioned_at (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre (i + 1 ) )
.

Definition partition_xy_points_return_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_same_outside_range pts_l (point_swap (pts_cur) ((i + 1 )) (high_pre)) low_pre high_pre )
.

Definition partition_xy_points_return_wit_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_permutation pts_l (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
.

Definition partition_xy_points_return_wit_1_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (points_in_bound (point_swap (pts_cur) ((i + 1 )) (high_pre)) )
.

Definition partition_xy_points_return_wit_1_split_goal_5 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((Zlength (pts_cur)) = n_pre)) (PreH2 : ((i + 1 ) <> high_pre)) (PreH3 : (j >= high_pre)) (PreH4 : ((Zlength (pts_cur)) = n_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH15 : (points_in_bound pts_cur )) (PreH16 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH17 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((Zlength ((point_swap (pts_cur) ((i + 1 )) (high_pre)))) = n_pre)
.

Definition partition_xy_points_return_wit_2 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (PointArray.full pts_pre n_pre pts_cur )
|--
  EX (pts_out: (@list Point)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out low_pre high_pre ) ” 
  &&  “ (point_xy_partitioned_at pts_out low_pre high_pre (i + 1 ) ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (point_xy_partitioned_at pts_cur low_pre high_pre (i + 1 ) ) ” 
  &&  “ (point_same_outside_range pts_l pts_cur low_pre high_pre ) ” 
  &&  “ (point_permutation pts_l pts_cur ) ”
  &&  emp
).

Definition partition_xy_points_return_wit_2_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_xy_partitioned_at pts_cur low_pre high_pre (i + 1 ) )
.

Definition partition_xy_points_return_wit_2_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_same_outside_range pts_l pts_cur low_pre high_pre )
.

Definition partition_xy_points_return_wit_2_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  (point_permutation pts_l pts_cur )
.

Definition partition_xy_points_partial_solve_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ”
  &&  ((&(((pts_pre + (high_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth high_pre pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre high_pre 0 n_pre pts_l )
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth high_pre pts_l __default_Point))))
.

Definition partition_xy_points_partial_solve_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point))  __default_Point (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ”
  &&  ((&(((pts_pre + (high_pre * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth high_pre pts_l __default_Point))))
  **  (PointArray.missing_i pts_pre high_pre 0 n_pre pts_l )
  **  ((&(((pts_pre + (high_pre * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth high_pre pts_l __default_Point))))
.

Definition partition_xy_points_partial_solve_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j < high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH15 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
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
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts_pre + (j * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre j 0 n_pre pts_cur )
  **  ((&(((pts_pre + (j * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
.

Definition partition_xy_points_partial_solve_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j < high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH15 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
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
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts_pre + (j * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  (PointArray.missing_i pts_pre j 0 n_pre pts_cur )
  **  ((&(((pts_pre + (j * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
.

Definition partition_xy_points_partial_solve_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : (j < high_pre)) (PreH2 : ((Zlength (pts_cur)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH13 : (points_in_bound pts_cur )) (PreH14 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH15 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
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
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_xy_points_partial_solve_wit_6_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |-> retval)
  **  (PointArray.full pts_pre n_pre pts_cur )
  **  ((( &( "ay" ) )) # Int  |-> (point_y ((Znth j pts_cur __default_Point))))
  **  ((( &( "ax" ) )) # Int  |-> (point_x ((Znth j pts_cur __default_Point))))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
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

Definition partition_xy_points_partial_solve_wit_6_aux := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point)) (retval: Z)  __default_Point (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : ((Zlength (pts_cur)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : ((low_pre - 1 ) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH15 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH16 : (points_in_bound pts_cur )) (PreH17 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH18 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
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
  &&  “ (retval = (point_cmp_leftdown ((point_mk ((point_x ((Znth j pts_cur __default_Point)))) ((point_y ((Znth j pts_cur __default_Point)))))) ((point_mk (pivot_x) (pivot_y))))) ” 
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
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_xy_points_partial_solve_wit_6 := partition_xy_points_partial_solve_wit_6_pure -> partition_xy_points_partial_solve_wit_6_aux.

Definition partition_xy_points_partial_solve_wit_7_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
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

Definition partition_xy_points_partial_solve_wit_7_aux := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pivot_y: Z) (pivot_x: Z) (j: Z) (i: Z) (pts_cur: (@list Point))  __default_Point (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : ((Zlength (pts_cur)) = n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : (((Znth high_pre pts_cur __default_Point).(x) ) = pivot_x)) (PreH13 : (((Znth high_pre pts_cur __default_Point).(y) ) = pivot_y)) (PreH14 : (points_in_bound pts_cur )) (PreH15 : (point_in_bound (point_mk (pivot_x) (pivot_y)) )) (PreH16 : (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j )) ,
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
  &&  “ (point_in_bound (point_mk (pivot_x) (pivot_y)) ) ” 
  &&  “ (point_xy_partition_scan_inv pts_l pts_cur low_pre high_pre (point_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointArray.full pts_pre n_pre pts_cur )
.

Definition partition_xy_points_partial_solve_wit_7 := partition_xy_points_partial_solve_wit_7_pure -> partition_xy_points_partial_solve_wit_7_aux.

(*----- Function quicksort_xy_points -----*)

Definition quicksort_xy_points_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : ((Zlength (pts_out)) = n_pre)) (PreH5 : (points_in_bound pts_out )) (PreH6 : (point_permutation pts_l pts_out )) (PreH7 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH8 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 50000)) (PreH12 : (0 <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < n_pre)) (PreH15 : ((Zlength (pts_l)) = n_pre)) (PreH16 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quicksort_xy_points_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : ((Zlength (pts_out)) = n_pre)) (PreH5 : (points_in_bound pts_out )) (PreH6 : (point_permutation pts_l pts_out )) (PreH7 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH8 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 50000)) (PreH12 : (0 <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < n_pre)) (PreH15 : ((Zlength (pts_l)) = n_pre)) (PreH16 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_xy_points_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (point_permutation pts_l pts_out )) (PreH8 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH9 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH10 : (left_pre < right_pre)) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : ((Zlength (pts_l)) = n_pre)) (PreH17 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ False ”
.

Definition quicksort_xy_points_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (pts_out_2: (@list Point)) (PreH1 : (retval < right_pre)) (PreH2 : ((Zlength (pts_out_2)) = n_pre)) (PreH3 : (points_in_bound pts_out_2 )) (PreH4 : (point_permutation pts_out pts_out_2 )) (PreH5 : (point_same_outside_range pts_out pts_out_2 left_pre (retval - 1 ) )) (PreH6 : (point_xy_sorted_range pts_out_2 left_pre (retval - 1 ) )) (PreH7 : (retval > left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out)) = n_pre)) (PreH11 : (points_in_bound pts_out )) (PreH12 : (point_permutation pts_l pts_out )) (PreH13 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_xy_points_safety_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (pts_out_2: (@list Point)) (PreH1 : (retval < right_pre)) (PreH2 : ((Zlength (pts_out_2)) = n_pre)) (PreH3 : (points_in_bound pts_out_2 )) (PreH4 : (point_permutation pts_out pts_out_2 )) (PreH5 : (point_same_outside_range pts_out pts_out_2 left_pre (retval - 1 ) )) (PreH6 : (point_xy_sorted_range pts_out_2 left_pre (retval - 1 ) )) (PreH7 : (retval > left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out)) = n_pre)) (PreH11 : (points_in_bound pts_out )) (PreH12 : (point_permutation pts_l pts_out )) (PreH13 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_xy_points_safety_wit_6 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (point_permutation pts_l pts_out )) (PreH8 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH9 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH10 : (left_pre < right_pre)) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : ((Zlength (pts_l)) = n_pre)) (PreH17 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_xy_points_safety_wit_7 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (point_permutation pts_l pts_out )) (PreH8 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH9 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH10 : (left_pre < right_pre)) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : ((Zlength (pts_l)) = n_pre)) (PreH17 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_xy_points_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (point_permutation pts_out_3 pts_out_4 )) (PreH4 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : ((Zlength (pts_out_3)) = n_pre)) (PreH8 : (points_in_bound pts_out_3 )) (PreH9 : (point_permutation pts_out_2 pts_out_3 )) (PreH10 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH11 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH12 : (retval > left_pre)) (PreH13 : (left_pre <= retval)) (PreH14 : (retval <= right_pre)) (PreH15 : ((Zlength (pts_out_2)) = n_pre)) (PreH16 : (points_in_bound pts_out_2 )) (PreH17 : (point_permutation pts_l pts_out_2 )) (PreH18 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH19 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH20 : (left_pre < right_pre)) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : (0 <= left_pre)) (PreH24 : ((-1) <= right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : ((Zlength (pts_l)) = n_pre)) (PreH27 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out_4 )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_xy_sorted_range pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (point_permutation pts_out_3 pts_out_4 )) (PreH4 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : ((Zlength (pts_out_3)) = n_pre)) (PreH8 : (points_in_bound pts_out_3 )) (PreH9 : (point_permutation pts_out_2 pts_out_3 )) (PreH10 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH11 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH12 : (retval > left_pre)) (PreH13 : (left_pre <= retval)) (PreH14 : (retval <= right_pre)) (PreH15 : ((Zlength (pts_out_2)) = n_pre)) (PreH16 : (points_in_bound pts_out_2 )) (PreH17 : (point_permutation pts_l pts_out_2 )) (PreH18 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH19 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH20 : (left_pre < right_pre)) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : (0 <= left_pre)) (PreH24 : ((-1) <= right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : ((Zlength (pts_l)) = n_pre)) (PreH27 : (points_in_bound pts_l )) ,
  TT && emp 
|--
  “ (point_xy_sorted_range pts_out_4 left_pre right_pre ) ” 
  &&  “ (point_same_outside_range pts_l pts_out_4 left_pre right_pre ) ” 
  &&  “ (point_permutation pts_l pts_out_4 ) ”
  &&  emp
).

Definition quicksort_xy_points_return_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (point_permutation pts_out_3 pts_out_4 )) (PreH4 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : ((Zlength (pts_out_3)) = n_pre)) (PreH8 : (points_in_bound pts_out_3 )) (PreH9 : (point_permutation pts_out_2 pts_out_3 )) (PreH10 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH11 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH12 : (retval > left_pre)) (PreH13 : (left_pre <= retval)) (PreH14 : (retval <= right_pre)) (PreH15 : ((Zlength (pts_out_2)) = n_pre)) (PreH16 : (points_in_bound pts_out_2 )) (PreH17 : (point_permutation pts_l pts_out_2 )) (PreH18 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH19 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH20 : (left_pre < right_pre)) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : (0 <= left_pre)) (PreH24 : ((-1) <= right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : ((Zlength (pts_l)) = n_pre)) (PreH27 : (points_in_bound pts_l )) ,
  (point_xy_sorted_range pts_out_4 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (point_permutation pts_out_3 pts_out_4 )) (PreH4 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : ((Zlength (pts_out_3)) = n_pre)) (PreH8 : (points_in_bound pts_out_3 )) (PreH9 : (point_permutation pts_out_2 pts_out_3 )) (PreH10 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH11 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH12 : (retval > left_pre)) (PreH13 : (left_pre <= retval)) (PreH14 : (retval <= right_pre)) (PreH15 : ((Zlength (pts_out_2)) = n_pre)) (PreH16 : (points_in_bound pts_out_2 )) (PreH17 : (point_permutation pts_l pts_out_2 )) (PreH18 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH19 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH20 : (left_pre < right_pre)) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : (0 <= left_pre)) (PreH24 : ((-1) <= right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : ((Zlength (pts_l)) = n_pre)) (PreH27 : (points_in_bound pts_l )) ,
  (point_same_outside_range pts_l pts_out_4 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_1_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (pts_out_4: (@list Point)) (PreH1 : ((Zlength (pts_out_4)) = n_pre)) (PreH2 : (points_in_bound pts_out_4 )) (PreH3 : (point_permutation pts_out_3 pts_out_4 )) (PreH4 : (point_same_outside_range pts_out_3 pts_out_4 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_4 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : ((Zlength (pts_out_3)) = n_pre)) (PreH8 : (points_in_bound pts_out_3 )) (PreH9 : (point_permutation pts_out_2 pts_out_3 )) (PreH10 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH11 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH12 : (retval > left_pre)) (PreH13 : (left_pre <= retval)) (PreH14 : (retval <= right_pre)) (PreH15 : ((Zlength (pts_out_2)) = n_pre)) (PreH16 : (points_in_bound pts_out_2 )) (PreH17 : (point_permutation pts_l pts_out_2 )) (PreH18 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH19 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH20 : (left_pre < right_pre)) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : (0 <= left_pre)) (PreH24 : ((-1) <= right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : ((Zlength (pts_l)) = n_pre)) (PreH27 : (points_in_bound pts_l )) ,
  (point_permutation pts_l pts_out_4 )
.

Definition quicksort_xy_points_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (point_permutation pts_out_2 pts_out_3 )) (PreH4 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : (retval <= left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out_3 )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_xy_sorted_range pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (point_permutation pts_out_2 pts_out_3 )) (PreH4 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : (retval <= left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  TT && emp 
|--
  “ (point_xy_sorted_range pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_same_outside_range pts_l pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_permutation pts_l pts_out_3 ) ”
  &&  emp
).

Definition quicksort_xy_points_return_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (point_permutation pts_out_2 pts_out_3 )) (PreH4 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : (retval <= left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (point_xy_sorted_range pts_out_3 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_2_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (point_permutation pts_out_2 pts_out_3 )) (PreH4 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : (retval <= left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (point_same_outside_range pts_l pts_out_3 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_2_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : ((Zlength (pts_out_3)) = n_pre)) (PreH2 : (points_in_bound pts_out_3 )) (PreH3 : (point_permutation pts_out_2 pts_out_3 )) (PreH4 : (point_same_outside_range pts_out_2 pts_out_3 (retval + 1 ) right_pre )) (PreH5 : (point_xy_sorted_range pts_out_3 (retval + 1 ) right_pre )) (PreH6 : (retval < right_pre)) (PreH7 : (retval <= left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (point_permutation pts_l pts_out_3 )
.

Definition quicksort_xy_points_return_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH6 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (retval > left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out_3 )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_xy_sorted_range pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH6 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (retval > left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  TT && emp 
|--
  “ (point_xy_sorted_range pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_same_outside_range pts_l pts_out_3 left_pre right_pre ) ” 
  &&  “ (point_permutation pts_l pts_out_3 ) ”
  &&  emp
).

Definition quicksort_xy_points_return_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH6 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (retval > left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (point_xy_sorted_range pts_out_3 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_3_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH6 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (retval > left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (point_same_outside_range pts_l pts_out_3 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_3_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out_3: (@list Point)) (PreH1 : (retval >= right_pre)) (PreH2 : ((Zlength (pts_out_3)) = n_pre)) (PreH3 : (points_in_bound pts_out_3 )) (PreH4 : (point_permutation pts_out_2 pts_out_3 )) (PreH5 : (point_same_outside_range pts_out_2 pts_out_3 left_pre (retval - 1 ) )) (PreH6 : (point_xy_sorted_range pts_out_3 left_pre (retval - 1 ) )) (PreH7 : (retval > left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (point_permutation pts_l pts_out_3 )
.

Definition quicksort_xy_points_return_wit_4 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  EX (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_xy_sorted_range pts_out left_pre right_pre ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) ,
  TT && emp 
|--
  “ (point_xy_sorted_range pts_l left_pre right_pre ) ” 
  &&  “ (point_same_outside_range pts_l pts_l left_pre right_pre ) ” 
  &&  “ (point_permutation pts_l pts_l ) ”
  &&  emp
).

Definition quicksort_xy_points_return_wit_4_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) ,
  (point_xy_sorted_range pts_l left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_4_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) ,
  (point_same_outside_range pts_l pts_l left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_4_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) ,
  (point_permutation pts_l pts_l )
.

Definition quicksort_xy_points_partial_solve_wit_1_pure := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) ,
  ((( &( "p" ) )) # Int  |->_)
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
.

Definition quicksort_xy_points_partial_solve_wit_1_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
.

Definition quicksort_xy_points_partial_solve_wit_1 := quicksort_xy_points_partial_solve_wit_1_pure -> quicksort_xy_points_partial_solve_wit_1_aux.

Definition quicksort_xy_points_partial_solve_wit_2_pure := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : ((Zlength (pts_out)) = n_pre)) (PreH5 : (points_in_bound pts_out )) (PreH6 : (point_permutation pts_l pts_out )) (PreH7 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH8 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 50000)) (PreH12 : (0 <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < n_pre)) (PreH15 : ((Zlength (pts_l)) = n_pre)) (PreH16 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
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
.

Definition quicksort_xy_points_partial_solve_wit_2_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : ((Zlength (pts_out)) = n_pre)) (PreH5 : (points_in_bound pts_out )) (PreH6 : (point_permutation pts_l pts_out )) (PreH7 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH8 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH9 : (left_pre < right_pre)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 50000)) (PreH12 : (0 <= left_pre)) (PreH13 : ((-1) <= right_pre)) (PreH14 : (right_pre < n_pre)) (PreH15 : ((Zlength (pts_l)) = n_pre)) (PreH16 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_xy_partitioned_at pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_xy_points_partial_solve_wit_2 := quicksort_xy_points_partial_solve_wit_2_pure -> quicksort_xy_points_partial_solve_wit_2_aux.

Definition quicksort_xy_points_partial_solve_wit_3_pure := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out: (@list Point)) (PreH1 : (retval < right_pre)) (PreH2 : ((Zlength (pts_out)) = n_pre)) (PreH3 : (points_in_bound pts_out )) (PreH4 : (point_permutation pts_out_2 pts_out )) (PreH5 : (point_same_outside_range pts_out_2 pts_out left_pre (retval - 1 ) )) (PreH6 : (point_xy_sorted_range pts_out left_pre (retval - 1 ) )) (PreH7 : (retval > left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
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
.

Definition quicksort_xy_points_partial_solve_wit_3_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (pts_out: (@list Point)) (PreH1 : (retval < right_pre)) (PreH2 : ((Zlength (pts_out)) = n_pre)) (PreH3 : (points_in_bound pts_out )) (PreH4 : (point_permutation pts_out_2 pts_out )) (PreH5 : (point_same_outside_range pts_out_2 pts_out left_pre (retval - 1 ) )) (PreH6 : (point_xy_sorted_range pts_out left_pre (retval - 1 ) )) (PreH7 : (retval > left_pre)) (PreH8 : (left_pre <= retval)) (PreH9 : (retval <= right_pre)) (PreH10 : ((Zlength (pts_out_2)) = n_pre)) (PreH11 : (points_in_bound pts_out_2 )) (PreH12 : (point_permutation pts_l pts_out_2 )) (PreH13 : (point_same_outside_range pts_l pts_out_2 left_pre right_pre )) (PreH14 : (point_xy_partitioned_at pts_out_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_out_2 pts_out ) ” 
  &&  “ (point_same_outside_range pts_out_2 pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (point_xy_sorted_range pts_out left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (points_in_bound pts_out_2 ) ” 
  &&  “ (point_permutation pts_l pts_out_2 ) ” 
  &&  “ (point_same_outside_range pts_l pts_out_2 left_pre right_pre ) ” 
  &&  “ (point_xy_partitioned_at pts_out_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_xy_points_partial_solve_wit_3 := quicksort_xy_points_partial_solve_wit_3_pure -> quicksort_xy_points_partial_solve_wit_3_aux.

Definition quicksort_xy_points_partial_solve_wit_4_pure := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (point_permutation pts_l pts_out )) (PreH8 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH9 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH10 : (left_pre < right_pre)) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : ((Zlength (pts_l)) = n_pre)) (PreH17 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  ((( &( "p" ) )) # Int  |-> retval)
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
.

Definition quicksort_xy_points_partial_solve_wit_4_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : ((Zlength (pts_out)) = n_pre)) (PreH6 : (points_in_bound pts_out )) (PreH7 : (point_permutation pts_l pts_out )) (PreH8 : (point_same_outside_range pts_l pts_out left_pre right_pre )) (PreH9 : (point_xy_partitioned_at pts_out left_pre right_pre retval )) (PreH10 : (left_pre < right_pre)) (PreH11 : (0 <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : ((Zlength (pts_l)) = n_pre)) (PreH17 : (points_in_bound pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_same_outside_range pts_l pts_out left_pre right_pre ) ” 
  &&  “ (point_xy_partitioned_at pts_out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
.

Definition quicksort_xy_points_partial_solve_wit_4 := quicksort_xy_points_partial_solve_wit_4_pure -> quicksort_xy_points_partial_solve_wit_4_aux.

(*----- Function andrew_build_from_sorted -----*)

Definition andrew_build_from_sorted_safety_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH4 : (points_in_bound pts_l_low_level_spec )) (PreH5 : (points_not_all_same pts_l_low_level_spec )) (PreH6 : (point_xy_sorted pts_l_low_level_spec )) (PreH7 : (safeExec (equiv (empty_point_stack)) (andrew_monotone_chain_m (pts_l_low_level_spec)) X_low_level_spec )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l_low_level_spec )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition andrew_build_from_sorted_safety_wit_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH4 : (points_in_bound pts_l_low_level_spec )) (PreH5 : (points_not_all_same pts_l_low_level_spec )) (PreH6 : (point_xy_sorted pts_l_low_level_spec )) (PreH7 : (safeExec (equiv (empty_point_stack)) (andrew_monotone_chain_m (pts_l_low_level_spec)) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l_low_level_spec )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition andrew_build_from_sorted_safety_wit_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (0 <= i)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= k)) (PreH4 : (k <= i)) (PreH5 : ((0 < i) -> (1 <= k))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH9 : ((Zlength (pts_sorted)) = n_pre)) (PreH10 : (points_in_bound pts_sorted )) (PreH11 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH12 : (point_xy_sorted pts_sorted )) (PreH13 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH14 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH15 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_4 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_5 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_6 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_7 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_8 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_9 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_10 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition andrew_build_from_sorted_safety_wit_11 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition andrew_build_from_sorted_safety_wit_12 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH2 : (k >= 2)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= i)) (PreH7 : ((0 < i) -> (1 <= k))) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH11 : ((Zlength (pts_sorted)) = n_pre)) (PreH12 : (points_in_bound pts_sorted )) (PreH13 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH14 : (point_xy_sorted pts_sorted )) (PreH15 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH16 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH17 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH18 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition andrew_build_from_sorted_safety_wit_13 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k >= 2)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((0 < i) -> (1 <= k))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH18 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH19 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_14 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k < 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.seg hull_pre 0 k lower )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_15 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k >= 2)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((0 < i) -> (1 <= k))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH18 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH19 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_16 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k < 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.seg hull_pre 0 k lower )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_17 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k >= 2)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((0 < i) -> (1 <= k))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH18 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH19 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_18 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH15 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lower_n" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((n_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_19 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH15 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lower_n" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_20 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (0 <= (i + 1 ))) (PreH2 : ((i + 1 ) <= (n_pre - 1 ))) (PreH3 : (2 <= lower_n)) (PreH4 : (lower_n <= k)) (PreH5 : (k <= (2 * n_pre ))) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH9 : ((Zlength (pts_sorted)) = n_pre)) (PreH10 : (points_in_bound pts_sorted )) (PreH11 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH12 : (point_xy_sorted pts_sorted )) (PreH13 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH14 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition andrew_build_from_sorted_safety_wit_21 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_22 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_23 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_24 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_25 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_26 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_27 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition andrew_build_from_sorted_safety_wit_28 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition andrew_build_from_sorted_safety_wit_29 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH2 : (k > lower_n)) (PreH3 : (0 <= i)) (PreH4 : (i <= (n_pre - 2 ))) (PreH5 : (2 <= lower_n)) (PreH6 : (lower_n <= k)) (PreH7 : (k < (2 * n_pre ))) (PreH8 : (2 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH11 : ((Zlength (pts_sorted)) = n_pre)) (PreH12 : (points_in_bound pts_sorted )) (PreH13 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH14 : (point_xy_sorted pts_sorted )) (PreH15 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH16 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH17 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition andrew_build_from_sorted_safety_wit_30 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k > lower_n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH18 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_31 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.seg hull_pre 0 k hull_cur )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_32 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k > lower_n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH18 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_33 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.seg hull_pre 0 k hull_cur )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_34 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k > lower_n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH18 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_35 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (0 <= (i + 1 ))) (PreH3 : ((i + 1 ) <= (n_pre - 1 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k <= (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH15 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_entail_wit_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH4 : (points_in_bound pts_l_low_level_spec )) (PreH5 : (points_not_all_same pts_l_low_level_spec )) (PreH6 : (point_xy_sorted pts_l_low_level_spec )) (PreH7 : (safeExec (equiv (empty_point_stack)) (andrew_monotone_chain_m (pts_l_low_level_spec)) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_l_low_level_spec )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  EX (lower: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 < 0) -> (1 <= 0)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower 0 0 ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (0)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= 0) -> (safeExec (equiv ((rev ((sublist ((0 - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (0) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 0 lower )
  **  (PointArray.undef_seg hull_pre 0 (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH4 : (points_in_bound pts_l_low_level_spec )) (PreH5 : (points_not_all_same pts_l_low_level_spec )) (PreH6 : (point_xy_sorted pts_l_low_level_spec )) (PreH7 : (safeExec (equiv (empty_point_stack)) (andrew_monotone_chain_m (pts_l_low_level_spec)) X_low_level_spec )) ,
  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (safeExec (equiv ((rev ((@nil Point))))) (andrew_lower_cont (pts_l_low_level_spec) (0)) X_low_level_spec ) ” 
  &&  “ (andrew_lower_scan_inv pts_l_low_level_spec (@nil Point) 0 0 ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_l_low_level_spec ) ”
  &&  (PointArray.undef_seg hull_pre 0 (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_1_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH4 : (points_in_bound pts_l_low_level_spec )) (PreH5 : (points_not_all_same pts_l_low_level_spec )) (PreH6 : (point_xy_sorted pts_l_low_level_spec )) (PreH7 : (safeExec (equiv (empty_point_stack)) (andrew_monotone_chain_m (pts_l_low_level_spec)) X_low_level_spec )) ,
  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (safeExec (equiv ((rev ((@nil Point))))) (andrew_lower_cont (pts_l_low_level_spec) (0)) X_low_level_spec ) ”
.

Definition andrew_build_from_sorted_entail_wit_1_split_goal_2 := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH4 : (points_in_bound pts_l_low_level_spec )) (PreH5 : (points_not_all_same pts_l_low_level_spec )) (PreH6 : (point_xy_sorted pts_l_low_level_spec )) (PreH7 : (safeExec (equiv (empty_point_stack)) (andrew_monotone_chain_m (pts_l_low_level_spec)) X_low_level_spec )) ,
  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (andrew_lower_scan_inv pts_l_low_level_spec (@nil Point) 0 0 ) ”
.

Definition andrew_build_from_sorted_entail_wit_1_split_goal_3 := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH4 : (points_in_bound pts_l_low_level_spec )) (PreH5 : (points_not_all_same pts_l_low_level_spec )) (PreH6 : (point_xy_sorted pts_l_low_level_spec )) (PreH7 : (safeExec (equiv (empty_point_stack)) (andrew_monotone_chain_m (pts_l_low_level_spec)) X_low_level_spec )) ,
  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (point_permutation pts_l_low_level_spec pts_l_low_level_spec ) ”
.

Definition andrew_build_from_sorted_entail_wit_1_split_goal_spatial := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH4 : (points_in_bound pts_l_low_level_spec )) (PreH5 : (points_not_all_same pts_l_low_level_spec )) (PreH6 : (point_xy_sorted pts_l_low_level_spec )) (PreH7 : (safeExec (equiv (empty_point_stack)) (andrew_monotone_chain_m (pts_l_low_level_spec)) X_low_level_spec )) ,
  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  (PointArray.undef_seg hull_pre 0 (2 * n_pre ) )
.

Definition andrew_build_from_sorted_entail_wit_2 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH15 : (safeExec (equiv ((rev (lower_2)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  (PointArray.seg hull_pre 0 k lower_2 )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (lower: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH15 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (point_in_bound (Znth i pts_sorted_2 __default_Point) ) ”
  &&  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_2_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH15 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (point_in_bound (Znth i pts_sorted_2 __default_Point) ) ”
.

Definition andrew_build_from_sorted_entail_wit_2_split_goal_spatial := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH15 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_entail_wit_3 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower_2 __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower_2 __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower_2 __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower_2 __default_Point)))) ((point_x ((Znth i pts_sorted_2 __default_Point)))) ((point_y ((Znth i pts_sorted_2 __default_Point))))))) (PreH3 : (k >= 2)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((0 < i) -> (1 <= k))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH13 : (points_in_bound pts_sorted_2 )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH15 : (point_xy_sorted pts_sorted_2 )) (PreH16 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH17 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH18 : (safeExec (equiv ((rev (lower_2)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH19 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  (PointArray.seg hull_pre 0 k lower_2 )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (lower: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (k - 1 )) ” 
  &&  “ ((k - 1 ) <= i) ” 
  &&  “ ((0 < i) -> (1 <= (k - 1 ))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i (k - 1 ) ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist (((k - 1 ) - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) ((k - 1 )) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 (k - 1 ) lower )
  **  (PointArray.undef_seg hull_pre (k - 1 ) (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower_2 __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower_2 __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower_2 __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower_2 __default_Point)))) ((point_x ((Znth i pts_sorted_2 __default_Point)))) ((point_y ((Znth i pts_sorted_2 __default_Point))))))) (PreH3 : (k >= 2)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((0 < i) -> (1 <= k))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH13 : (points_in_bound pts_sorted_2 )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH15 : (point_xy_sorted pts_sorted_2 )) (PreH16 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH17 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH18 : (safeExec (equiv ((rev (lower_2)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH19 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower_2 )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (lower: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (k - 1 )) ” 
  &&  “ ((k - 1 ) <= i) ” 
  &&  “ ((0 < i) -> (1 <= (k - 1 ))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted_2 ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted_2 ) ” 
  &&  “ (point_xy_sorted pts_sorted_2 ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted_2 __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted_2 lower i (k - 1 ) ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist (((k - 1 ) - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) ((k - 1 )) (lower))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec )) ”
  &&  (PointArray.seg hull_pre 0 (k - 1 ) lower )
  **  (PointArray.undef_seg hull_pre (k - 1 ) (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_4_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k < 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH16 : (safeExec (equiv ((rev (lower_2)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower_2 )
|--
  EX (lower: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (i + 1 )) ” 
  &&  “ ((0 < (i + 1 )) -> (1 <= (k + 1 ))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower (i + 1 ) (k + 1 ) ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= (i + 1 )) -> (safeExec (equiv ((rev ((sublist (((k + 1 ) - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) ((k + 1 )) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 (k + 1 ) lower )
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : ((point_y ((Znth i pts_sorted_2 __default_Point))) <= INT_MAX)) (PreH2 : ((point_x ((Znth i pts_sorted_2 __default_Point))) <= INT_MAX)) (PreH3 : ((point_y ((Znth i pts_sorted_2 __default_Point))) >= INT_MIN)) (PreH4 : ((point_x ((Znth i pts_sorted_2 __default_Point))) >= INT_MIN)) (PreH5 : (k < 2)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : ((0 < i) -> (1 <= k))) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH15 : (points_in_bound pts_sorted_2 )) (PreH16 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH17 : (point_xy_sorted pts_sorted_2 )) (PreH18 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH19 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH20 : (safeExec (equiv ((rev (lower_2)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH21 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower_2 )
|--
  EX (lower: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (i + 1 )) ” 
  &&  “ ((0 < (i + 1 )) -> (1 <= (k + 1 ))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted_2 ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted_2 ) ” 
  &&  “ (point_xy_sorted pts_sorted_2 ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted_2 lower (i + 1 ) (k + 1 ) ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted_2) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted_2)) <= (i + 1 )) -> (safeExec (equiv ((rev ((sublist (((k + 1 ) - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) ((k + 1 )) (lower))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec )) ”
  &&  (PointArray.seg hull_pre 0 (k + 1 ) lower )
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_4_2 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower_2 __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower_2 __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower_2 __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower_2 __default_Point)))) ((point_x ((Znth i pts_sorted_2 __default_Point)))) ((point_y ((Znth i pts_sorted_2 __default_Point))))))) (PreH3 : (k >= 2)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((0 < i) -> (1 <= k))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH13 : (points_in_bound pts_sorted_2 )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH15 : (point_xy_sorted pts_sorted_2 )) (PreH16 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH17 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH18 : (safeExec (equiv ((rev (lower_2)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH19 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower_2 )
|--
  EX (lower: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (i + 1 )) ” 
  &&  “ ((0 < (i + 1 )) -> (1 <= (k + 1 ))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower (i + 1 ) (k + 1 ) ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= (i + 1 )) -> (safeExec (equiv ((rev ((sublist (((k + 1 ) - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) ((k + 1 )) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 (k + 1 ) lower )
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : ((point_y ((Znth i pts_sorted_2 __default_Point))) <= INT_MAX)) (PreH2 : ((point_x ((Znth i pts_sorted_2 __default_Point))) <= INT_MAX)) (PreH3 : ((point_y ((Znth i pts_sorted_2 __default_Point))) >= INT_MIN)) (PreH4 : ((point_x ((Znth i pts_sorted_2 __default_Point))) >= INT_MIN)) (PreH5 : (retval > 0)) (PreH6 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower_2 __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower_2 __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower_2 __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower_2 __default_Point)))) ((point_x ((Znth i pts_sorted_2 __default_Point)))) ((point_y ((Znth i pts_sorted_2 __default_Point))))))) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH17 : (points_in_bound pts_sorted_2 )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH19 : (point_xy_sorted pts_sorted_2 )) (PreH20 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted_2 lower_2 i k )) (PreH22 : (safeExec (equiv ((rev (lower_2)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower_2))) (lower_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower_2))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower_2 )
|--
  EX (lower: (@list Point)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (i + 1 )) ” 
  &&  “ ((0 < (i + 1 )) -> (1 <= (k + 1 ))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted_2 ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted_2 ) ” 
  &&  “ (point_xy_sorted pts_sorted_2 ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted_2 lower (i + 1 ) (k + 1 ) ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted_2) ((i + 1 ))) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted_2)) <= (i + 1 )) -> (safeExec (equiv ((rev ((sublist (((k + 1 ) - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) ((k + 1 )) (lower))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec )) ”
  &&  (PointArray.seg hull_pre 0 (k + 1 ) lower )
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_5 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower i k )) (PreH15 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (hull_cur: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= ((n_pre - 2 ) + 1 )) ” 
  &&  “ (((n_pre - 2 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (2 <= k) ” 
  &&  “ (k <= k) ” 
  &&  “ (k <= (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur ((n_pre - 2 ) + 1 ) k k ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (hull_cur))) (((n_pre - 2 ) + 1 ))) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower i k )) (PreH15 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower))) (((n_pre - 2 ) + 1 ))) X_low_level_spec ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted_2 lower ((n_pre - 2 ) + 1 ) k k ) ” 
  &&  “ (2 <= k) ”
  &&  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_5_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower i k )) (PreH15 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower))) (((n_pre - 2 ) + 1 ))) X_low_level_spec ) ”
.

Definition andrew_build_from_sorted_entail_wit_5_split_goal_2 := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower i k )) (PreH15 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (andrew_upper_scan_inv pts_sorted_2 lower ((n_pre - 2 ) + 1 ) k k ) ”
.

Definition andrew_build_from_sorted_entail_wit_5_split_goal_3 := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower i k )) (PreH15 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (2 <= k) ”
.

Definition andrew_build_from_sorted_entail_wit_5_split_goal_spatial := 
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_lower_scan_inv pts_sorted_2 lower i k )) (PreH15 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted_2) (i)) X_low_level_spec )) (PreH16 : (((Zlength (pts_sorted_2)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted_2)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_entail_wit_6 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (i >= 0)) (PreH2 : (0 <= (i + 1 ))) (PreH3 : ((i + 1 ) <= (n_pre - 1 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k <= (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) (PreH15 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur_2))) (hull_cur_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur_2))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  (PointArray.seg hull_pre 0 k hull_cur_2 )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (hull_cur: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (i >= 0)) (PreH2 : (0 <= (i + 1 ))) (PreH3 : ((i + 1 ) <= (n_pre - 1 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k <= (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (point_in_bound (Znth i pts_sorted_2 __default_Point) ) ” 
  &&  “ (k < (2 * n_pre )) ”
  &&  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_6_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (i >= 0)) (PreH2 : (0 <= (i + 1 ))) (PreH3 : ((i + 1 ) <= (n_pre - 1 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k <= (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (point_in_bound (Znth i pts_sorted_2 __default_Point) ) ”
.

Definition andrew_build_from_sorted_entail_wit_6_split_goal_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (0 <= (i + 1 ))) (PreH3 : ((i + 1 ) <= (n_pre - 1 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k <= (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k < (2 * n_pre )) ”
.

Definition andrew_build_from_sorted_entail_wit_6_split_goal_spatial := 
forall (hull_pre: Z) (n_pre: Z) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (0 <= (i + 1 ))) (PreH3 : ((i + 1 ) <= (n_pre - 1 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k <= (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) ,
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_entail_wit_7 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur_2 __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur_2 __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur_2 __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur_2 __default_Point)))) ((point_x ((Znth i pts_sorted_2 __default_Point)))) ((point_y ((Znth i pts_sorted_2 __default_Point))))))) (PreH3 : (k > lower_n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH13 : (points_in_bound pts_sorted_2 )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH15 : (point_xy_sorted pts_sorted_2 )) (PreH16 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH17 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) (PreH18 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur_2))) (hull_cur_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur_2))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  (PointArray.seg hull_pre 0 k hull_cur_2 )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (hull_cur: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= (k - 1 )) ” 
  &&  “ ((k - 1 ) < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) (k - 1 ) lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 (k - 1 ) hull_cur )
  **  (PointArray.undef_seg hull_pre (k - 1 ) (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval <= 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur_2 __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur_2 __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur_2 __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur_2 __default_Point)))) ((point_x ((Znth i pts_sorted_2 __default_Point)))) ((point_y ((Znth i pts_sorted_2 __default_Point))))))) (PreH3 : (k > lower_n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH13 : (points_in_bound pts_sorted_2 )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH15 : (point_xy_sorted pts_sorted_2 )) (PreH16 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH17 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) (PreH18 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur_2))) (hull_cur_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur_2))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur_2 )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (hull_cur: (@list Point)) ,
  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= (k - 1 )) ” 
  &&  “ ((k - 1 ) < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted_2 ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted_2 ) ” 
  &&  “ (point_xy_sorted pts_sorted_2 ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted_2 __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted_2 hull_cur (i + 1 ) (k - 1 ) lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (k - 1 ) hull_cur )
  **  (PointArray.undef_seg hull_pre (k - 1 ) (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_8_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur_2))) (hull_cur_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur_2))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur_2 )
|--
  EX (hull_cur: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur ((i - 1 ) + 1 ) (k + 1 ) lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) (((i - 1 ) + 1 ))) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 (k + 1 ) hull_cur )
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : ((point_y ((Znth i pts_sorted_2 __default_Point))) <= INT_MAX)) (PreH2 : ((point_x ((Znth i pts_sorted_2 __default_Point))) <= INT_MAX)) (PreH3 : ((point_y ((Znth i pts_sorted_2 __default_Point))) >= INT_MIN)) (PreH4 : ((point_x ((Znth i pts_sorted_2 __default_Point))) >= INT_MIN)) (PreH5 : (k <= lower_n)) (PreH6 : (0 <= i)) (PreH7 : (i <= (n_pre - 2 ))) (PreH8 : (2 <= lower_n)) (PreH9 : (lower_n <= k)) (PreH10 : (k < (2 * n_pre ))) (PreH11 : (2 <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH14 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH15 : (points_in_bound pts_sorted_2 )) (PreH16 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH17 : (point_xy_sorted pts_sorted_2 )) (PreH18 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH19 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) (PreH20 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur_2))) (hull_cur_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur_2))) ((i + 1 ))) X_low_level_spec )) ,
  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur_2 )
|--
  EX (hull_cur: (@list Point)) ,
  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted_2 ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted_2 ) ” 
  &&  “ (point_xy_sorted pts_sorted_2 ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted_2 hull_cur ((i - 1 ) + 1 ) (k + 1 ) lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur))) (((i - 1 ) + 1 ))) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (k + 1 ) hull_cur )
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_8_2 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur_2 __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur_2 __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur_2 __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur_2 __default_Point)))) ((point_x ((Znth i pts_sorted_2 __default_Point)))) ((point_y ((Znth i pts_sorted_2 __default_Point))))))) (PreH3 : (k > lower_n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH13 : (points_in_bound pts_sorted_2 )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH15 : (point_xy_sorted pts_sorted_2 )) (PreH16 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH17 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) (PreH18 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur_2))) (hull_cur_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur_2))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur_2 )
|--
  EX (hull_cur: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur ((i - 1 ) + 1 ) (k + 1 ) lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) (((i - 1 ) + 1 ))) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 (k + 1 ) hull_cur )
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur_2: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : ((point_y ((Znth i pts_sorted_2 __default_Point))) <= INT_MAX)) (PreH2 : ((point_x ((Znth i pts_sorted_2 __default_Point))) <= INT_MAX)) (PreH3 : ((point_y ((Znth i pts_sorted_2 __default_Point))) >= INT_MIN)) (PreH4 : ((point_x ((Znth i pts_sorted_2 __default_Point))) >= INT_MIN)) (PreH5 : (retval > 0)) (PreH6 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur_2 __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur_2 __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur_2 __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur_2 __default_Point)))) ((point_x ((Znth i pts_sorted_2 __default_Point)))) ((point_y ((Znth i pts_sorted_2 __default_Point))))))) (PreH7 : (k > lower_n)) (PreH8 : (0 <= i)) (PreH9 : (i <= (n_pre - 2 ))) (PreH10 : (2 <= lower_n)) (PreH11 : (lower_n <= k)) (PreH12 : (k < (2 * n_pre ))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH17 : (points_in_bound pts_sorted_2 )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH19 : (point_xy_sorted pts_sorted_2 )) (PreH20 : (point_in_bound (Znth i pts_sorted_2 __default_Point) )) (PreH21 : (andrew_upper_scan_inv pts_sorted_2 hull_cur_2 (i + 1 ) k lower_n )) (PreH22 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur_2))) (hull_cur_2)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur_2))) ((i + 1 ))) X_low_level_spec )) ,
  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted_2 __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur_2 )
|--
  EX (hull_cur: (@list Point)) ,
  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted_2 ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted_2 ) ” 
  &&  “ (point_xy_sorted pts_sorted_2 ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted_2 hull_cur ((i - 1 ) + 1 ) (k + 1 ) lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur))) (((i - 1 ) + 1 ))) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (k + 1 ) hull_cur )
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
).

Definition andrew_build_from_sorted_entail_wit_9 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (0 <= (i + 1 ))) (PreH3 : ((i + 1 ) <= (n_pre - 1 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k <= (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_upper_scan_inv pts_sorted_2 hull_cur (i + 1 ) k lower_n )) (PreH15 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted_2 )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (hull_out: (@list Point))  (pts_sorted: (@list Point)) ,
  “ (2 <= (k - 1 )) ” 
  &&  “ ((k - 1 ) <= (2 * n_pre )) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ ((Zlength (hull_out)) = (k - 1 )) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (safeExec (equiv ((rev (hull_out)))) (return (tt)) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 (k - 1 ) hull_out )
  **  (PointArray.undef_seg hull_pre (k - 1 ) (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted_2: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (0 <= (i + 1 ))) (PreH3 : ((i + 1 ) <= (n_pre - 1 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k <= (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted_2)) = n_pre)) (PreH11 : (points_in_bound pts_sorted_2 )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted_2 )) (PreH13 : (point_xy_sorted pts_sorted_2 )) (PreH14 : (andrew_upper_scan_inv pts_sorted_2 hull_cur (i + 1 ) k lower_n )) (PreH15 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted_2) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (hull_out: (@list Point)) ,
  “ (2 <= (k - 1 )) ” 
  &&  “ ((k - 1 ) <= (2 * n_pre )) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted_2)) = n_pre) ” 
  &&  “ ((Zlength (hull_out)) = (k - 1 )) ” 
  &&  “ (points_in_bound pts_sorted_2 ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted_2 ) ” 
  &&  “ (point_xy_sorted pts_sorted_2 ) ” 
  &&  “ (safeExec (equiv ((rev (hull_out)))) (return (tt)) X_low_level_spec ) ”
  &&  (PointArray.seg hull_pre 0 (k - 1 ) hull_out )
  **  (PointArray.undef_seg hull_pre (k - 1 ) (2 * n_pre ) )
).

Definition andrew_build_from_sorted_return_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (pts_sorted: (@list Point)) (hull_out_2: (@list Point)) (k: Z) (PreH1 : (2 <= k)) (PreH2 : (k <= (2 * n_pre ))) (PreH3 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH4 : ((Zlength (pts_sorted)) = n_pre)) (PreH5 : ((Zlength (hull_out_2)) = k)) (PreH6 : (points_in_bound pts_sorted )) (PreH7 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH8 : (point_xy_sorted pts_sorted )) (PreH9 : (safeExec (equiv ((rev (hull_out_2)))) (return (tt)) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_out_2 )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  EX (hull_out: (@list Point))  (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (2 <= k) ” 
  &&  “ (k <= (2 * n_pre )) ” 
  &&  “ ((Zlength (hull_out)) = k) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_out ) ” 
  &&  “ (point_xy_sorted pts_out ) ” 
  &&  “ (safeExec (equiv ((rev (hull_out)))) (return (tt)) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  (PointArray.seg hull_pre 0 k hull_out )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point))))
  **  (PointArray.missing_i hull_pre (k - 2 ) 0 k lower )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point))))
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point))))
  **  (PointArray.missing_i hull_pre (k - 2 ) 0 k lower )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point))))
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((hull_pre + ((k - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point))))
  **  (PointArray.missing_i hull_pre (k - 1 ) 0 k lower )
  **  ((&(((hull_pre + ((k - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point))))
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_4 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((hull_pre + ((k - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point))))
  **  (PointArray.missing_i hull_pre (k - 1 ) 0 k lower )
  **  ((&(((hull_pre + ((k - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point))))
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_5 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_6 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_x ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_x ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_y ((Znth i pts_sorted __default_Point))) <= point_bound) ”
).

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_4 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_5 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_6 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_7 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_8 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_9 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_x ((Znth i pts_sorted __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_10 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_x ((Znth i pts_sorted __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_11 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_y ((Znth i pts_sorted __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_12 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (n_pre <= INT_MAX)) (PreH3 : (i <= INT_MAX)) (PreH4 : (k >= INT_MIN)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (k >= 2)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= k)) (PreH11 : (k <= i)) (PreH12 : ((0 < i) -> (1 <= k))) (PreH13 : (2 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH16 : ((Zlength (pts_sorted)) = n_pre)) (PreH17 : (points_in_bound pts_sorted )) (PreH18 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH19 : (point_xy_sorted pts_sorted )) (PreH20 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH21 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH22 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH23 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth i pts_sorted __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_7_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k >= 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_x ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ” 
  &&  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_7 := andrew_build_from_sorted_partial_solve_wit_7_pure -> andrew_build_from_sorted_partial_solve_wit_7_aux.

Definition andrew_build_from_sorted_partial_solve_wit_8 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k < 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k < 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_9 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k < 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k < 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
.

Definition andrew_build_from_sorted_partial_solve_wit_10 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k >= 2)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((0 < i) -> (1 <= k))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH18 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH19 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point)))))) ” 
  &&  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_11 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k >= 2)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((0 < i) -> (1 <= k))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH18 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH19 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point)))))) ” 
  &&  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
.

Definition andrew_build_from_sorted_partial_solve_wit_12 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z)  __default_Point (PreH1 : (k < 2)) (PreH2 : (0 <= i)) (PreH3 : (i < n_pre)) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : ((0 < i) -> (1 <= k))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH16 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH17 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
|--
  “ (k < 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.seg hull_pre 0 k lower )
.

Definition andrew_build_from_sorted_partial_solve_wit_13 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (lower: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k >= 2)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((0 < i) -> (1 <= k))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_lower_scan_inv pts_sorted lower i k )) (PreH18 : (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec )) (PreH19 : (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec ))) ,
  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k lower )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) lower __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) lower __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point)))))) ” 
  &&  “ (k >= 2) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((0 < i) -> (1 <= k)) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_lower_scan_inv pts_sorted lower i k ) ” 
  &&  “ (safeExec (equiv ((rev (lower)))) (andrew_lower_cont (pts_sorted) (i)) X_low_level_spec ) ” 
  &&  “ (((Zlength (pts_sorted)) <= i) -> (safeExec (equiv ((rev ((sublist ((k - 1 )) ((Zlength (lower))) (lower)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (k) (lower))) (((Zlength (pts_sorted)) - 1 ))) X_low_level_spec )) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.seg hull_pre 0 k lower )
.

Definition andrew_build_from_sorted_partial_solve_wit_14 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))))
  **  (PointArray.missing_i hull_pre (k - 2 ) 0 k hull_cur )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))))
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_15 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))))
  **  (PointArray.missing_i hull_pre (k - 2 ) 0 k hull_cur )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))))
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_16 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((k - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))))
  **  (PointArray.missing_i hull_pre (k - 1 ) 0 k hull_cur )
  **  ((&(((hull_pre + ((k - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))))
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_17 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((hull_pre + ((k - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))))
  **  (PointArray.missing_i hull_pre (k - 1 ) 0 k hull_cur )
  **  ((&(((hull_pre + ((k - 1 ) * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))))
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_18 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_19 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_x ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_x ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_y ((Znth i pts_sorted __default_Point))) <= point_bound) ”
).

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_4 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_5 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_6 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_7 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_8 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_9 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_x ((Znth i pts_sorted __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_10 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_x ((Znth i pts_sorted __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_11 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((-point_bound) <= (point_y ((Znth i pts_sorted __default_Point)))) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_12 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= INT_MAX)) (PreH2 : (lower_n <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (k >= INT_MIN)) (PreH6 : (lower_n >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (k > lower_n)) (PreH10 : (0 <= i)) (PreH11 : (i <= (n_pre - 2 ))) (PreH12 : (2 <= lower_n)) (PreH13 : (lower_n <= k)) (PreH14 : (k < (2 * n_pre ))) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH18 : ((Zlength (pts_sorted)) = n_pre)) (PreH19 : (points_in_bound pts_sorted )) (PreH20 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH21 : (point_xy_sorted pts_sorted )) (PreH22 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH23 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH24 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth i pts_sorted __default_Point))) <= point_bound) ”
.

Definition andrew_build_from_sorted_partial_solve_wit_20_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k > lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ ((point_y ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_x ((Znth i pts_sorted __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth i pts_sorted __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point))) <= point_bound) ” 
  &&  “ ((-point_bound) <= (point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ” 
  &&  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_20 := andrew_build_from_sorted_partial_solve_wit_20_pure -> andrew_build_from_sorted_partial_solve_wit_20_aux.

Definition andrew_build_from_sorted_partial_solve_wit_21 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k <= lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_22 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (k <= lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
.

Definition andrew_build_from_sorted_partial_solve_wit_23 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k > lower_n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH18 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point)))))) ” 
  &&  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
.

Definition andrew_build_from_sorted_partial_solve_wit_24 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k > lower_n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH18 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
  **  (PointArray.undef_seg hull_pre k (2 * n_pre ) )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point)))))) ” 
  &&  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |->_)
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
.

Definition andrew_build_from_sorted_partial_solve_wit_25 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z)  __default_Point (PreH1 : (k <= lower_n)) (PreH2 : (0 <= i)) (PreH3 : (i <= (n_pre - 2 ))) (PreH4 : (2 <= lower_n)) (PreH5 : (lower_n <= k)) (PreH6 : (k < (2 * n_pre ))) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH10 : ((Zlength (pts_sorted)) = n_pre)) (PreH11 : (points_in_bound pts_sorted )) (PreH12 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH13 : (point_xy_sorted pts_sorted )) (PreH14 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH15 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH16 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
|--
  “ (k <= lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.seg hull_pre 0 k hull_cur )
.

Definition andrew_build_from_sorted_partial_solve_wit_26 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) (pts_l_low_level_spec: (@list Point)) (hull_cur: (@list Point)) (pts_sorted: (@list Point)) (k: Z) (lower_n: Z) (i: Z) (retval: Z)  __default_Point (PreH1 : (retval > 0)) (PreH2 : (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point))))))) (PreH3 : (k > lower_n)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l_low_level_spec)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (point_permutation pts_l_low_level_spec pts_sorted )) (PreH15 : (point_xy_sorted pts_sorted )) (PreH16 : (point_in_bound (Znth i pts_sorted __default_Point) )) (PreH17 : (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n )) (PreH18 : (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec )) ,
  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.seg hull_pre 0 k hull_cur )
|--
  “ (retval > 0) ” 
  &&  “ (retval = (point_cross_by_value ((point_x ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 2 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_y ((Znth ((k - 1 ) - 0 ) hull_cur __default_Point)))) ((point_x ((Znth i pts_sorted __default_Point)))) ((point_y ((Znth i pts_sorted __default_Point)))))) ” 
  &&  “ (k > lower_n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (point_in_bound (Znth i pts_sorted __default_Point) ) ” 
  &&  “ (andrew_upper_scan_inv pts_sorted hull_cur (i + 1 ) k lower_n ) ” 
  &&  “ (safeExec (equiv ((rev ((sublist ((lower_n - 1 )) ((Zlength (hull_cur))) (hull_cur)))))) (andrew_upper_cont (pts_sorted) ((sublist (0) (lower_n) (hull_cur))) ((i + 1 ))) X_low_level_spec ) ”
  &&  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |-> (point_y ((Znth i pts_sorted __default_Point))))
  **  (PointArray.missing_i pts_pre i 0 n_pre pts_sorted )
  **  ((&(((pts_pre + (i * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "x")) # Int  |-> (point_x ((Znth i pts_sorted __default_Point))))
  **  (PointArray.undef_seg hull_pre (k + 1 ) (2 * n_pre ) )
  **  ((&(((hull_pre + (k * sizeof( "Point" ))))  # "Point" ->ₛ "y")) # Int  |->_)
  **  (PointArray.seg hull_pre 0 k hull_cur )
.

(*----- Function andrew_monotone_chain -----*)

Definition andrew_monotone_chain_safety_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) ,
  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition andrew_monotone_chain_safety_wit_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) ,
  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition andrew_monotone_chain_safety_wit_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) ,
  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition andrew_monotone_chain_entail_wit_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (PreH1 : ((Zlength (pts_out)) = n_pre)) (PreH2 : (points_in_bound pts_out )) (PreH3 : (point_permutation pts_l pts_out )) (PreH4 : (point_same_outside_range pts_l pts_out 0 (n_pre - 1 ) )) (PreH5 : (point_xy_sorted_range pts_out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (pts_l)) = n_pre)) (PreH9 : (points_in_bound pts_l )) (PreH10 : (points_not_all_same pts_l )) ,
  (PointArray.full pts_pre n_pre pts_out )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  EX (pts_sorted: (@list Point)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (points_not_all_same pts_sorted ) ” 
  &&  “ (point_permutation pts_l pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
) \/
(
forall (n_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (PreH1 : ((Zlength (pts_out)) = n_pre)) (PreH2 : (points_in_bound pts_out )) (PreH3 : (point_permutation pts_l pts_out )) (PreH4 : (point_same_outside_range pts_l pts_out 0 (n_pre - 1 ) )) (PreH5 : (point_xy_sorted_range pts_out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (pts_l)) = n_pre)) (PreH9 : (points_in_bound pts_l )) (PreH10 : (points_not_all_same pts_l )) ,
  TT && emp 
|--
  “ (point_xy_sorted pts_out ) ” 
  &&  “ (points_not_all_same pts_out ) ”
  &&  emp
).

Definition andrew_monotone_chain_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (PreH1 : ((Zlength (pts_out)) = n_pre)) (PreH2 : (points_in_bound pts_out )) (PreH3 : (point_permutation pts_l pts_out )) (PreH4 : (point_same_outside_range pts_l pts_out 0 (n_pre - 1 ) )) (PreH5 : (point_xy_sorted_range pts_out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (pts_l)) = n_pre)) (PreH9 : (points_in_bound pts_l )) (PreH10 : (points_not_all_same pts_l )) ,
  (point_xy_sorted pts_out )
.

Definition andrew_monotone_chain_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (pts_l: (@list Point)) (pts_out: (@list Point)) (PreH1 : ((Zlength (pts_out)) = n_pre)) (PreH2 : (points_in_bound pts_out )) (PreH3 : (point_permutation pts_l pts_out )) (PreH4 : (point_same_outside_range pts_l pts_out 0 (n_pre - 1 ) )) (PreH5 : (point_xy_sorted_range pts_out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (pts_l)) = n_pre)) (PreH9 : (points_in_bound pts_l )) (PreH10 : (points_not_all_same pts_l )) ,
  (points_not_all_same pts_out )
.

Definition andrew_monotone_chain_return_wit_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_sorted: (@list Point)) (hull_out_2: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (PreH1 : ((Zlength (pts_out_2)) = n_pre)) (PreH2 : (2 <= retval)) (PreH3 : (retval <= (2 * n_pre ))) (PreH4 : ((Zlength (hull_out_2)) = retval)) (PreH5 : (points_in_bound pts_out_2 )) (PreH6 : (point_permutation pts_sorted pts_out_2 )) (PreH7 : (point_xy_sorted pts_out_2 )) (PreH8 : (is_convex_hull pts_sorted hull_out_2 )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (points_not_all_same pts_sorted )) (PreH15 : (point_permutation pts_l pts_sorted )) (PreH16 : (point_xy_sorted pts_sorted )) ,
  (PointArray.full pts_pre n_pre pts_out_2 )
  **  (PointArray.seg hull_pre 0 retval hull_out_2 )
  **  (PointArray.undef_seg hull_pre retval (2 * n_pre ) )
|--
  EX (hull_out: (@list Point))  (pts_out: (@list Point)) ,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (2 <= retval) ” 
  &&  “ (retval <= (2 * n_pre )) ” 
  &&  “ ((Zlength (hull_out)) = retval) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l pts_out ) ” 
  &&  “ (point_xy_sorted pts_out ) ” 
  &&  “ (is_convex_hull pts_l hull_out ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  (PointArray.seg hull_pre 0 retval hull_out )
  **  (PointArray.undef_seg hull_pre retval (2 * n_pre ) )
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_sorted: (@list Point)) (hull_out_2: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (PreH1 : ((Zlength (pts_out_2)) = n_pre)) (PreH2 : (2 <= retval)) (PreH3 : (retval <= (2 * n_pre ))) (PreH4 : ((Zlength (hull_out_2)) = retval)) (PreH5 : (points_in_bound pts_out_2 )) (PreH6 : (point_permutation pts_sorted pts_out_2 )) (PreH7 : (point_xy_sorted pts_out_2 )) (PreH8 : (is_convex_hull pts_sorted hull_out_2 )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (points_not_all_same pts_sorted )) (PreH15 : (point_permutation pts_l pts_sorted )) (PreH16 : (point_xy_sorted pts_sorted )) ,
  (PointArray.undef_seg hull_pre retval (2 * n_pre ) )
|--
  “ (is_convex_hull pts_l hull_out_2 ) ” 
  &&  “ (point_permutation pts_l pts_out_2 ) ”
  &&  (PointArray.undef_seg hull_pre retval (2 * n_pre ) )
).

Definition andrew_monotone_chain_return_wit_1_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_sorted: (@list Point)) (hull_out_2: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (PreH1 : ((Zlength (pts_out_2)) = n_pre)) (PreH2 : (2 <= retval)) (PreH3 : (retval <= (2 * n_pre ))) (PreH4 : ((Zlength (hull_out_2)) = retval)) (PreH5 : (points_in_bound pts_out_2 )) (PreH6 : (point_permutation pts_sorted pts_out_2 )) (PreH7 : (point_xy_sorted pts_out_2 )) (PreH8 : (is_convex_hull pts_sorted hull_out_2 )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (points_not_all_same pts_sorted )) (PreH15 : (point_permutation pts_l pts_sorted )) (PreH16 : (point_xy_sorted pts_sorted )) ,
  (PointArray.undef_seg hull_pre retval (2 * n_pre ) )
|--
  “ (is_convex_hull pts_l hull_out_2 ) ”
.

Definition andrew_monotone_chain_return_wit_1_split_goal_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_sorted: (@list Point)) (hull_out_2: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (PreH1 : ((Zlength (pts_out_2)) = n_pre)) (PreH2 : (2 <= retval)) (PreH3 : (retval <= (2 * n_pre ))) (PreH4 : ((Zlength (hull_out_2)) = retval)) (PreH5 : (points_in_bound pts_out_2 )) (PreH6 : (point_permutation pts_sorted pts_out_2 )) (PreH7 : (point_xy_sorted pts_out_2 )) (PreH8 : (is_convex_hull pts_sorted hull_out_2 )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (points_not_all_same pts_sorted )) (PreH15 : (point_permutation pts_l pts_sorted )) (PreH16 : (point_xy_sorted pts_sorted )) ,
  (PointArray.undef_seg hull_pre retval (2 * n_pre ) )
|--
  “ (point_permutation pts_l pts_out_2 ) ”
.

Definition andrew_monotone_chain_return_wit_1_split_goal_spatial := 
forall (hull_pre: Z) (n_pre: Z) (pts_l: (@list Point)) (pts_sorted: (@list Point)) (hull_out_2: (@list Point)) (pts_out_2: (@list Point)) (retval: Z) (PreH1 : ((Zlength (pts_out_2)) = n_pre)) (PreH2 : (2 <= retval)) (PreH3 : (retval <= (2 * n_pre ))) (PreH4 : ((Zlength (hull_out_2)) = retval)) (PreH5 : (points_in_bound pts_out_2 )) (PreH6 : (point_permutation pts_sorted pts_out_2 )) (PreH7 : (point_xy_sorted pts_out_2 )) (PreH8 : (is_convex_hull pts_sorted hull_out_2 )) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((Zlength (pts_l)) = n_pre)) (PreH12 : ((Zlength (pts_sorted)) = n_pre)) (PreH13 : (points_in_bound pts_sorted )) (PreH14 : (points_not_all_same pts_sorted )) (PreH15 : (point_permutation pts_l pts_sorted )) (PreH16 : (point_xy_sorted pts_sorted )) ,
  (PointArray.undef_seg hull_pre retval (2 * n_pre ) )
|--
  (PointArray.undef_seg hull_pre retval (2 * n_pre ) )
.

Definition andrew_monotone_chain_partial_solve_wit_1_pure := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) ,
  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ”
.

Definition andrew_monotone_chain_partial_solve_wit_1_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (points_in_bound pts_l )) (PreH5 : (points_not_all_same pts_l )) ,
  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ (points_in_bound pts_l ) ” 
  &&  “ (points_not_all_same pts_l ) ”
  &&  (PointArray.full pts_pre n_pre pts_l )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
.

Definition andrew_monotone_chain_partial_solve_wit_1 := andrew_monotone_chain_partial_solve_wit_1_pure -> andrew_monotone_chain_partial_solve_wit_1_aux.

Definition andrew_monotone_chain_partial_solve_wit_2_pure := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_sorted: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : ((Zlength (pts_sorted)) = n_pre)) (PreH5 : (points_in_bound pts_sorted )) (PreH6 : (points_not_all_same pts_sorted )) (PreH7 : (point_permutation pts_l pts_sorted )) (PreH8 : (point_xy_sorted pts_sorted )) ,
  ((( &( "ret" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (points_not_all_same pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ”
.

Definition andrew_monotone_chain_partial_solve_wit_2_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l: (@list Point)) (pts_sorted: (@list Point)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : ((Zlength (pts_sorted)) = n_pre)) (PreH5 : (points_in_bound pts_sorted )) (PreH6 : (points_not_all_same pts_sorted )) (PreH7 : (point_permutation pts_l pts_sorted )) (PreH8 : (point_xy_sorted pts_sorted )) ,
  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (points_not_all_same pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l)) = n_pre) ” 
  &&  “ ((Zlength (pts_sorted)) = n_pre) ” 
  &&  “ (points_in_bound pts_sorted ) ” 
  &&  “ (points_not_all_same pts_sorted ) ” 
  &&  “ (point_permutation pts_l pts_sorted ) ” 
  &&  “ (point_xy_sorted pts_sorted ) ”
  &&  (PointArray.full pts_pre n_pre pts_sorted )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
.

Definition andrew_monotone_chain_partial_solve_wit_2 := andrew_monotone_chain_partial_solve_wit_2_pure -> andrew_monotone_chain_partial_solve_wit_2_aux.

Definition andrew_build_from_sorted_derive_high_level_spec_by_low_level_spec := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (pts_l_high_level_spec: (@list Point)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_high_level_spec)) = n_pre) ” 
  &&  “ (points_in_bound pts_l_high_level_spec ) ” 
  &&  “ (points_not_all_same pts_l_high_level_spec ) ” 
  &&  “ (point_xy_sorted pts_l_high_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_l_high_level_spec )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) )
|--
EX (pts_l_low_level_spec: (@list Point)) (X_low_level_spec: (unit -> ((@list Point) -> Prop))) ,
  (“ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (pts_l_low_level_spec)) = n_pre) ” 
  &&  “ (points_in_bound pts_l_low_level_spec ) ” 
  &&  “ (points_not_all_same pts_l_low_level_spec ) ” 
  &&  “ (point_xy_sorted pts_l_low_level_spec ) ” 
  &&  “ (safeExec (equiv (empty_point_stack)) (andrew_monotone_chain_m (pts_l_low_level_spec)) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_l_low_level_spec )
  **  (PointArray.undef_full hull_pre (2 * n_pre ) ))
  **
  ((EX hull_out_2 pts_out_2 retval_2,
  “ ((Zlength (pts_out_2)) = n_pre) ” 
  &&  “ (2 <= retval_2) ” 
  &&  “ (retval_2 <= (2 * n_pre )) ” 
  &&  “ ((Zlength (hull_out_2)) = retval_2) ” 
  &&  “ (points_in_bound pts_out_2 ) ” 
  &&  “ (point_permutation pts_l_low_level_spec pts_out_2 ) ” 
  &&  “ (point_xy_sorted pts_out_2 ) ” 
  &&  “ (safeExec (equiv ((rev (hull_out_2)))) (return (tt)) X_low_level_spec ) ”
  &&  (PointArray.full pts_pre n_pre pts_out_2 )
  **  (PointArray.seg hull_pre 0 retval_2 hull_out_2 )
  **  (PointArray.undef_seg hull_pre retval_2 (2 * n_pre ) ))
  -*
  (EX hull_out pts_out retval,
  “ ((Zlength (pts_out)) = n_pre) ” 
  &&  “ (2 <= retval) ” 
  &&  “ (retval <= (2 * n_pre )) ” 
  &&  “ ((Zlength (hull_out)) = retval) ” 
  &&  “ (points_in_bound pts_out ) ” 
  &&  “ (point_permutation pts_l_high_level_spec pts_out ) ” 
  &&  “ (point_xy_sorted pts_out ) ” 
  &&  “ (is_convex_hull pts_l_high_level_spec hull_out ) ”
  &&  (PointArray.full pts_pre n_pre pts_out )
  **  (PointArray.seg hull_pre 0 retval hull_out )
  **  (PointArray.undef_seg hull_pre retval (2 * n_pre ) )))
.

Module Type VC_Correct.

Include point_array_Strategy_Correct.
Include safeexec_Strategy_Correct.

Axiom proof_of_cmp_xy_safety_wit_1 : cmp_xy_safety_wit_1.
Axiom proof_of_cmp_xy_safety_wit_2 : cmp_xy_safety_wit_2.
Axiom proof_of_cmp_xy_safety_wit_3 : cmp_xy_safety_wit_3.
Axiom proof_of_cmp_xy_safety_wit_4 : cmp_xy_safety_wit_4.
Axiom proof_of_cmp_xy_safety_wit_5 : cmp_xy_safety_wit_5.
Axiom proof_of_cmp_xy_safety_wit_6 : cmp_xy_safety_wit_6.
Axiom proof_of_cmp_xy_safety_wit_7 : cmp_xy_safety_wit_7.
Axiom proof_of_cmp_xy_entail_wit_1 : cmp_xy_entail_wit_1.
Axiom proof_of_cmp_xy_return_wit_1 : cmp_xy_return_wit_1.
Axiom proof_of_cmp_xy_return_wit_2 : cmp_xy_return_wit_2.
Axiom proof_of_cmp_xy_return_wit_3 : cmp_xy_return_wit_3.
Axiom proof_of_cmp_xy_return_wit_4 : cmp_xy_return_wit_4.
Axiom proof_of_cmp_xy_return_wit_5 : cmp_xy_return_wit_5.
Axiom proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Axiom proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Axiom proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Axiom proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Axiom proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Axiom proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Axiom proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Axiom proof_of_cross_prod_entail_wit_1 : cross_prod_entail_wit_1.
Axiom proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Axiom proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Axiom proof_of_swap_points_partial_solve_wit_1 : swap_points_partial_solve_wit_1.
Axiom proof_of_swap_points_partial_solve_wit_2 : swap_points_partial_solve_wit_2.
Axiom proof_of_swap_points_partial_solve_wit_3 : swap_points_partial_solve_wit_3.
Axiom proof_of_swap_points_partial_solve_wit_4 : swap_points_partial_solve_wit_4.
Axiom proof_of_swap_points_partial_solve_wit_5 : swap_points_partial_solve_wit_5.
Axiom proof_of_swap_points_partial_solve_wit_6 : swap_points_partial_solve_wit_6.
Axiom proof_of_swap_points_partial_solve_wit_7 : swap_points_partial_solve_wit_7.
Axiom proof_of_swap_points_partial_solve_wit_8 : swap_points_partial_solve_wit_8.
Axiom proof_of_partition_xy_points_safety_wit_1 : partition_xy_points_safety_wit_1.
Axiom proof_of_partition_xy_points_safety_wit_2 : partition_xy_points_safety_wit_2.
Axiom proof_of_partition_xy_points_safety_wit_3 : partition_xy_points_safety_wit_3.
Axiom proof_of_partition_xy_points_safety_wit_4 : partition_xy_points_safety_wit_4.
Axiom proof_of_partition_xy_points_safety_wit_5 : partition_xy_points_safety_wit_5.
Axiom proof_of_partition_xy_points_safety_wit_6 : partition_xy_points_safety_wit_6.
Axiom proof_of_partition_xy_points_safety_wit_7 : partition_xy_points_safety_wit_7.
Axiom proof_of_partition_xy_points_safety_wit_8 : partition_xy_points_safety_wit_8.
Axiom proof_of_partition_xy_points_entail_wit_1 : partition_xy_points_entail_wit_1.
Axiom proof_of_partition_xy_points_entail_wit_2_1 : partition_xy_points_entail_wit_2_1.
Axiom proof_of_partition_xy_points_entail_wit_2_2 : partition_xy_points_entail_wit_2_2.
Axiom proof_of_partition_xy_points_entail_wit_2_3 : partition_xy_points_entail_wit_2_3.
Axiom proof_of_partition_xy_points_return_wit_1 : partition_xy_points_return_wit_1.
Axiom proof_of_partition_xy_points_return_wit_2 : partition_xy_points_return_wit_2.
Axiom proof_of_partition_xy_points_partial_solve_wit_1 : partition_xy_points_partial_solve_wit_1.
Axiom proof_of_partition_xy_points_partial_solve_wit_2 : partition_xy_points_partial_solve_wit_2.
Axiom proof_of_partition_xy_points_partial_solve_wit_3 : partition_xy_points_partial_solve_wit_3.
Axiom proof_of_partition_xy_points_partial_solve_wit_4 : partition_xy_points_partial_solve_wit_4.
Axiom proof_of_partition_xy_points_partial_solve_wit_5 : partition_xy_points_partial_solve_wit_5.
Axiom proof_of_partition_xy_points_partial_solve_wit_6_pure : partition_xy_points_partial_solve_wit_6_pure.
Axiom proof_of_partition_xy_points_partial_solve_wit_6 : partition_xy_points_partial_solve_wit_6.
Axiom proof_of_partition_xy_points_partial_solve_wit_7_pure : partition_xy_points_partial_solve_wit_7_pure.
Axiom proof_of_partition_xy_points_partial_solve_wit_7 : partition_xy_points_partial_solve_wit_7.
Axiom proof_of_quicksort_xy_points_safety_wit_1 : quicksort_xy_points_safety_wit_1.
Axiom proof_of_quicksort_xy_points_safety_wit_2 : quicksort_xy_points_safety_wit_2.
Axiom proof_of_quicksort_xy_points_safety_wit_3 : quicksort_xy_points_safety_wit_3.
Axiom proof_of_quicksort_xy_points_safety_wit_4 : quicksort_xy_points_safety_wit_4.
Axiom proof_of_quicksort_xy_points_safety_wit_5 : quicksort_xy_points_safety_wit_5.
Axiom proof_of_quicksort_xy_points_safety_wit_6 : quicksort_xy_points_safety_wit_6.
Axiom proof_of_quicksort_xy_points_safety_wit_7 : quicksort_xy_points_safety_wit_7.
Axiom proof_of_quicksort_xy_points_return_wit_1 : quicksort_xy_points_return_wit_1.
Axiom proof_of_quicksort_xy_points_return_wit_2 : quicksort_xy_points_return_wit_2.
Axiom proof_of_quicksort_xy_points_return_wit_3 : quicksort_xy_points_return_wit_3.
Axiom proof_of_quicksort_xy_points_return_wit_4 : quicksort_xy_points_return_wit_4.
Axiom proof_of_quicksort_xy_points_partial_solve_wit_1_pure : quicksort_xy_points_partial_solve_wit_1_pure.
Axiom proof_of_quicksort_xy_points_partial_solve_wit_1 : quicksort_xy_points_partial_solve_wit_1.
Axiom proof_of_quicksort_xy_points_partial_solve_wit_2_pure : quicksort_xy_points_partial_solve_wit_2_pure.
Axiom proof_of_quicksort_xy_points_partial_solve_wit_2 : quicksort_xy_points_partial_solve_wit_2.
Axiom proof_of_quicksort_xy_points_partial_solve_wit_3_pure : quicksort_xy_points_partial_solve_wit_3_pure.
Axiom proof_of_quicksort_xy_points_partial_solve_wit_3 : quicksort_xy_points_partial_solve_wit_3.
Axiom proof_of_quicksort_xy_points_partial_solve_wit_4_pure : quicksort_xy_points_partial_solve_wit_4_pure.
Axiom proof_of_quicksort_xy_points_partial_solve_wit_4 : quicksort_xy_points_partial_solve_wit_4.
Axiom proof_of_andrew_build_from_sorted_safety_wit_1 : andrew_build_from_sorted_safety_wit_1.
Axiom proof_of_andrew_build_from_sorted_safety_wit_2 : andrew_build_from_sorted_safety_wit_2.
Axiom proof_of_andrew_build_from_sorted_safety_wit_3 : andrew_build_from_sorted_safety_wit_3.
Axiom proof_of_andrew_build_from_sorted_safety_wit_4 : andrew_build_from_sorted_safety_wit_4.
Axiom proof_of_andrew_build_from_sorted_safety_wit_5 : andrew_build_from_sorted_safety_wit_5.
Axiom proof_of_andrew_build_from_sorted_safety_wit_6 : andrew_build_from_sorted_safety_wit_6.
Axiom proof_of_andrew_build_from_sorted_safety_wit_7 : andrew_build_from_sorted_safety_wit_7.
Axiom proof_of_andrew_build_from_sorted_safety_wit_8 : andrew_build_from_sorted_safety_wit_8.
Axiom proof_of_andrew_build_from_sorted_safety_wit_9 : andrew_build_from_sorted_safety_wit_9.
Axiom proof_of_andrew_build_from_sorted_safety_wit_10 : andrew_build_from_sorted_safety_wit_10.
Axiom proof_of_andrew_build_from_sorted_safety_wit_11 : andrew_build_from_sorted_safety_wit_11.
Axiom proof_of_andrew_build_from_sorted_safety_wit_12 : andrew_build_from_sorted_safety_wit_12.
Axiom proof_of_andrew_build_from_sorted_safety_wit_13 : andrew_build_from_sorted_safety_wit_13.
Axiom proof_of_andrew_build_from_sorted_safety_wit_14 : andrew_build_from_sorted_safety_wit_14.
Axiom proof_of_andrew_build_from_sorted_safety_wit_15 : andrew_build_from_sorted_safety_wit_15.
Axiom proof_of_andrew_build_from_sorted_safety_wit_16 : andrew_build_from_sorted_safety_wit_16.
Axiom proof_of_andrew_build_from_sorted_safety_wit_17 : andrew_build_from_sorted_safety_wit_17.
Axiom proof_of_andrew_build_from_sorted_safety_wit_18 : andrew_build_from_sorted_safety_wit_18.
Axiom proof_of_andrew_build_from_sorted_safety_wit_19 : andrew_build_from_sorted_safety_wit_19.
Axiom proof_of_andrew_build_from_sorted_safety_wit_20 : andrew_build_from_sorted_safety_wit_20.
Axiom proof_of_andrew_build_from_sorted_safety_wit_21 : andrew_build_from_sorted_safety_wit_21.
Axiom proof_of_andrew_build_from_sorted_safety_wit_22 : andrew_build_from_sorted_safety_wit_22.
Axiom proof_of_andrew_build_from_sorted_safety_wit_23 : andrew_build_from_sorted_safety_wit_23.
Axiom proof_of_andrew_build_from_sorted_safety_wit_24 : andrew_build_from_sorted_safety_wit_24.
Axiom proof_of_andrew_build_from_sorted_safety_wit_25 : andrew_build_from_sorted_safety_wit_25.
Axiom proof_of_andrew_build_from_sorted_safety_wit_26 : andrew_build_from_sorted_safety_wit_26.
Axiom proof_of_andrew_build_from_sorted_safety_wit_27 : andrew_build_from_sorted_safety_wit_27.
Axiom proof_of_andrew_build_from_sorted_safety_wit_28 : andrew_build_from_sorted_safety_wit_28.
Axiom proof_of_andrew_build_from_sorted_safety_wit_29 : andrew_build_from_sorted_safety_wit_29.
Axiom proof_of_andrew_build_from_sorted_safety_wit_30 : andrew_build_from_sorted_safety_wit_30.
Axiom proof_of_andrew_build_from_sorted_safety_wit_31 : andrew_build_from_sorted_safety_wit_31.
Axiom proof_of_andrew_build_from_sorted_safety_wit_32 : andrew_build_from_sorted_safety_wit_32.
Axiom proof_of_andrew_build_from_sorted_safety_wit_33 : andrew_build_from_sorted_safety_wit_33.
Axiom proof_of_andrew_build_from_sorted_safety_wit_34 : andrew_build_from_sorted_safety_wit_34.
Axiom proof_of_andrew_build_from_sorted_safety_wit_35 : andrew_build_from_sorted_safety_wit_35.
Axiom proof_of_andrew_build_from_sorted_entail_wit_1 : andrew_build_from_sorted_entail_wit_1.
Axiom proof_of_andrew_build_from_sorted_entail_wit_2 : andrew_build_from_sorted_entail_wit_2.
Axiom proof_of_andrew_build_from_sorted_entail_wit_3 : andrew_build_from_sorted_entail_wit_3.
Axiom proof_of_andrew_build_from_sorted_entail_wit_4_1 : andrew_build_from_sorted_entail_wit_4_1.
Axiom proof_of_andrew_build_from_sorted_entail_wit_4_2 : andrew_build_from_sorted_entail_wit_4_2.
Axiom proof_of_andrew_build_from_sorted_entail_wit_5 : andrew_build_from_sorted_entail_wit_5.
Axiom proof_of_andrew_build_from_sorted_entail_wit_6 : andrew_build_from_sorted_entail_wit_6.
Axiom proof_of_andrew_build_from_sorted_entail_wit_7 : andrew_build_from_sorted_entail_wit_7.
Axiom proof_of_andrew_build_from_sorted_entail_wit_8_1 : andrew_build_from_sorted_entail_wit_8_1.
Axiom proof_of_andrew_build_from_sorted_entail_wit_8_2 : andrew_build_from_sorted_entail_wit_8_2.
Axiom proof_of_andrew_build_from_sorted_entail_wit_9 : andrew_build_from_sorted_entail_wit_9.
Axiom proof_of_andrew_build_from_sorted_return_wit_1 : andrew_build_from_sorted_return_wit_1.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_1 : andrew_build_from_sorted_partial_solve_wit_1.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_2 : andrew_build_from_sorted_partial_solve_wit_2.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_3 : andrew_build_from_sorted_partial_solve_wit_3.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_4 : andrew_build_from_sorted_partial_solve_wit_4.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_5 : andrew_build_from_sorted_partial_solve_wit_5.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_6 : andrew_build_from_sorted_partial_solve_wit_6.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure : andrew_build_from_sorted_partial_solve_wit_7_pure.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_7 : andrew_build_from_sorted_partial_solve_wit_7.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_8 : andrew_build_from_sorted_partial_solve_wit_8.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_9 : andrew_build_from_sorted_partial_solve_wit_9.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_10 : andrew_build_from_sorted_partial_solve_wit_10.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_11 : andrew_build_from_sorted_partial_solve_wit_11.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_12 : andrew_build_from_sorted_partial_solve_wit_12.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_13 : andrew_build_from_sorted_partial_solve_wit_13.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_14 : andrew_build_from_sorted_partial_solve_wit_14.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_15 : andrew_build_from_sorted_partial_solve_wit_15.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_16 : andrew_build_from_sorted_partial_solve_wit_16.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_17 : andrew_build_from_sorted_partial_solve_wit_17.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_18 : andrew_build_from_sorted_partial_solve_wit_18.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_19 : andrew_build_from_sorted_partial_solve_wit_19.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure : andrew_build_from_sorted_partial_solve_wit_20_pure.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_20 : andrew_build_from_sorted_partial_solve_wit_20.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_21 : andrew_build_from_sorted_partial_solve_wit_21.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_22 : andrew_build_from_sorted_partial_solve_wit_22.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_23 : andrew_build_from_sorted_partial_solve_wit_23.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_24 : andrew_build_from_sorted_partial_solve_wit_24.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_25 : andrew_build_from_sorted_partial_solve_wit_25.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_26 : andrew_build_from_sorted_partial_solve_wit_26.
Axiom proof_of_andrew_monotone_chain_safety_wit_1 : andrew_monotone_chain_safety_wit_1.
Axiom proof_of_andrew_monotone_chain_safety_wit_2 : andrew_monotone_chain_safety_wit_2.
Axiom proof_of_andrew_monotone_chain_safety_wit_3 : andrew_monotone_chain_safety_wit_3.
Axiom proof_of_andrew_monotone_chain_entail_wit_1 : andrew_monotone_chain_entail_wit_1.
Axiom proof_of_andrew_monotone_chain_return_wit_1 : andrew_monotone_chain_return_wit_1.
Axiom proof_of_andrew_monotone_chain_partial_solve_wit_1_pure : andrew_monotone_chain_partial_solve_wit_1_pure.
Axiom proof_of_andrew_monotone_chain_partial_solve_wit_1 : andrew_monotone_chain_partial_solve_wit_1.
Axiom proof_of_andrew_monotone_chain_partial_solve_wit_2_pure : andrew_monotone_chain_partial_solve_wit_2_pure.
Axiom proof_of_andrew_monotone_chain_partial_solve_wit_2 : andrew_monotone_chain_partial_solve_wit_2.
Axiom proof_of_andrew_build_from_sorted_derive_high_level_spec_by_low_level_spec : andrew_build_from_sorted_derive_high_level_spec_by_low_level_spec.

End VC_Correct.
