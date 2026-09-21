Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope R_scope.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.convex_hull_float.convex_hull_float_lib.
Local Open Scope sac.
From SimpleC.EE.LLM_bench.Algorithms.convex_hull_float Require Import pointf_array_strategy_goal.
From SimpleC.EE.LLM_bench.Algorithms.convex_hull_float Require Import pointf_array_strategy_proof.

(*----- Function point_cmp_xy -----*)

Definition point_cmp_xy_safety_wit_1 := 
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ax_pre ) ” 
  &&  “ (fp32_isFinite bx_pre ) ”
) \/
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ax_pre ) ” 
  &&  “ (fp32_isFinite bx_pre ) ”
).

Definition point_cmp_xy_safety_wit_1_split_goal_1 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ax_pre ) ”
.

Definition point_cmp_xy_safety_wit_1_split_goal_2 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite bx_pre ) ”
.

Definition point_cmp_xy_safety_wit_2 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ax_pre bx_pre )) (PreH2 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition point_cmp_xy_safety_wit_3 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ax_pre bx_pre )) (PreH2 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition point_cmp_xy_safety_wit_4 := 
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_ge ax_pre bx_pre )) (PreH2 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ax_pre ) ” 
  &&  “ (fp32_isFinite bx_pre ) ”
) \/
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_ge ax_pre bx_pre )) (PreH2 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ax_pre ) ” 
  &&  “ (fp32_isFinite bx_pre ) ”
).

Definition point_cmp_xy_safety_wit_4_split_goal_1 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_ge ax_pre bx_pre )) (PreH2 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ax_pre ) ”
.

Definition point_cmp_xy_safety_wit_4_split_goal_2 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_ge ax_pre bx_pre )) (PreH2 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite bx_pre ) ”
.

Definition point_cmp_xy_safety_wit_5 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_gt ax_pre bx_pre )) (PreH2 : (fp32_ge ax_pre bx_pre )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition point_cmp_xy_safety_wit_6 := 
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_le ax_pre bx_pre )) (PreH2 : (fp32_ge ax_pre bx_pre )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ay_pre ) ” 
  &&  “ (fp32_isFinite b_y_pre ) ”
) \/
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_le ax_pre bx_pre )) (PreH2 : (fp32_ge ax_pre bx_pre )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ay_pre ) ” 
  &&  “ (fp32_isFinite b_y_pre ) ”
).

Definition point_cmp_xy_safety_wit_6_split_goal_1 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_le ax_pre bx_pre )) (PreH2 : (fp32_ge ax_pre bx_pre )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ay_pre ) ”
.

Definition point_cmp_xy_safety_wit_6_split_goal_2 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_le ax_pre bx_pre )) (PreH2 : (fp32_ge ax_pre bx_pre )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite b_y_pre ) ”
.

Definition point_cmp_xy_safety_wit_7 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ay_pre b_y_pre )) (PreH2 : (fp32_le ax_pre bx_pre )) (PreH3 : (fp32_ge ax_pre bx_pre )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition point_cmp_xy_safety_wit_8 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ay_pre b_y_pre )) (PreH2 : (fp32_le ax_pre bx_pre )) (PreH3 : (fp32_ge ax_pre bx_pre )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition point_cmp_xy_safety_wit_9 := 
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_ge ay_pre b_y_pre )) (PreH2 : (fp32_le ax_pre bx_pre )) (PreH3 : (fp32_ge ax_pre bx_pre )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ay_pre ) ” 
  &&  “ (fp32_isFinite b_y_pre ) ”
) \/
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_ge ay_pre b_y_pre )) (PreH2 : (fp32_le ax_pre bx_pre )) (PreH3 : (fp32_ge ax_pre bx_pre )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ay_pre ) ” 
  &&  “ (fp32_isFinite b_y_pre ) ”
).

Definition point_cmp_xy_safety_wit_9_split_goal_1 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_ge ay_pre b_y_pre )) (PreH2 : (fp32_le ax_pre bx_pre )) (PreH3 : (fp32_ge ax_pre bx_pre )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite ay_pre ) ”
.

Definition point_cmp_xy_safety_wit_9_split_goal_2 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_ge ay_pre b_y_pre )) (PreH2 : (fp32_le ax_pre bx_pre )) (PreH3 : (fp32_ge ax_pre bx_pre )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (fp32_isFinite b_y_pre ) ”
.

Definition point_cmp_xy_safety_wit_10 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_gt ay_pre b_y_pre )) (PreH2 : (fp32_ge ay_pre b_y_pre )) (PreH3 : (fp32_le ax_pre bx_pre )) (PreH4 : (fp32_ge ax_pre bx_pre )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH8 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition point_cmp_xy_safety_wit_11 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_le ay_pre b_y_pre )) (PreH2 : (fp32_ge ay_pre b_y_pre )) (PreH3 : (fp32_le ax_pre bx_pre )) (PreH4 : (fp32_ge ax_pre bx_pre )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH8 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition point_cmp_xy_return_wit_1 := 
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_le ay_pre b_y_pre )) (PreH2 : (fp32_ge ay_pre b_y_pre )) (PreH3 : (fp32_le ax_pre bx_pre )) (PreH4 : (fp32_ge ax_pre bx_pre )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH8 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ (0 = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_le ay_pre b_y_pre )) (PreH2 : (fp32_ge ay_pre b_y_pre )) (PreH3 : (fp32_le ax_pre bx_pre )) (PreH4 : (fp32_ge ax_pre bx_pre )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH8 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ (0 = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
).

Definition point_cmp_xy_return_wit_1_split_goal_1 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_le ay_pre b_y_pre )) (PreH2 : (fp32_ge ay_pre b_y_pre )) (PreH3 : (fp32_le ax_pre bx_pre )) (PreH4 : (fp32_ge ax_pre bx_pre )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH8 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  (0 = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre)))))
.

Definition point_cmp_xy_return_wit_2 := 
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_gt ay_pre b_y_pre )) (PreH2 : (fp32_ge ay_pre b_y_pre )) (PreH3 : (fp32_le ax_pre bx_pre )) (PreH4 : (fp32_ge ax_pre bx_pre )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH8 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ (1 = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_gt ay_pre b_y_pre )) (PreH2 : (fp32_ge ay_pre b_y_pre )) (PreH3 : (fp32_le ax_pre bx_pre )) (PreH4 : (fp32_ge ax_pre bx_pre )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH8 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ (1 = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
).

Definition point_cmp_xy_return_wit_2_split_goal_1 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_gt ay_pre b_y_pre )) (PreH2 : (fp32_ge ay_pre b_y_pre )) (PreH3 : (fp32_le ax_pre bx_pre )) (PreH4 : (fp32_ge ax_pre bx_pre )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH8 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  (1 = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre)))))
.

Definition point_cmp_xy_return_wit_3 := 
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ay_pre b_y_pre )) (PreH2 : (fp32_le ax_pre bx_pre )) (PreH3 : (fp32_ge ax_pre bx_pre )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ ((-1) = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ay_pre b_y_pre )) (PreH2 : (fp32_le ax_pre bx_pre )) (PreH3 : (fp32_ge ax_pre bx_pre )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ ((-1) = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
).

Definition point_cmp_xy_return_wit_3_split_goal_1 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ay_pre b_y_pre )) (PreH2 : (fp32_le ax_pre bx_pre )) (PreH3 : (fp32_ge ax_pre bx_pre )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH7 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((-1) = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre)))))
.

Definition point_cmp_xy_return_wit_4 := 
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_gt ax_pre bx_pre )) (PreH2 : (fp32_ge ax_pre bx_pre )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ (1 = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_gt ax_pre bx_pre )) (PreH2 : (fp32_ge ax_pre bx_pre )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ (1 = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
).

Definition point_cmp_xy_return_wit_4_split_goal_1 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_gt ax_pre bx_pre )) (PreH2 : (fp32_ge ax_pre bx_pre )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  (1 = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre)))))
.

Definition point_cmp_xy_return_wit_5 := 
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ax_pre bx_pre )) (PreH2 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ ((-1) = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
) \/
(
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ax_pre bx_pre )) (PreH2 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  TT && emp 
|--
  “ ((-1) = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))))) ”
  &&  emp
).

Definition point_cmp_xy_return_wit_5_split_goal_1 := 
forall (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_lt ax_pre bx_pre )) (PreH2 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) ,
  ((-1) = (pointf_cmp_xy ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre)))))
.

(*----- Function point_cross -----*)

Definition point_cross_safety_wit_1 := 
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub (bx_pre) (ax_pre))) ((fp32_sub (cy_pre) (ay_pre))))) ((fp32_mul ((fp32_sub (b_y_pre) (ay_pre))) ((fp32_sub (cx_pre) (ax_pre)))))) ) ”
) \/
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub (bx_pre) (ax_pre))) ((fp32_sub (cy_pre) (ay_pre))))) ((fp32_mul ((fp32_sub (b_y_pre) (ay_pre))) ((fp32_sub (cx_pre) (ax_pre)))))) ) ”
).

Definition point_cross_safety_wit_1_split_goal_1 := 
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub (bx_pre) (ax_pre))) ((fp32_sub (cy_pre) (ay_pre))))) ((fp32_mul ((fp32_sub (b_y_pre) (ay_pre))) ((fp32_sub (cx_pre) (ax_pre)))))) ) ”
.

Definition point_cross_safety_wit_2 := 
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub (b_y_pre) (ay_pre))) ((fp32_sub (cx_pre) (ax_pre)))) ) ”
) \/
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub (b_y_pre) (ay_pre))) ((fp32_sub (cx_pre) (ax_pre)))) ) ”
).

Definition point_cross_safety_wit_2_split_goal_1 := 
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub (b_y_pre) (ay_pre))) ((fp32_sub (cx_pre) (ax_pre)))) ) ”
.

Definition point_cross_safety_wit_3 := 
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (cx_pre) (ax_pre)) ) ”
) \/
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (cx_pre) (ax_pre)) ) ”
).

Definition point_cross_safety_wit_3_split_goal_1 := 
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (cx_pre) (ax_pre)) ) ”
.

Definition point_cross_safety_wit_4 := 
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (b_y_pre) (ay_pre)) ) ”
) \/
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (b_y_pre) (ay_pre)) ) ”
).

Definition point_cross_safety_wit_4_split_goal_1 := 
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (b_y_pre) (ay_pre)) ) ”
.

Definition point_cross_safety_wit_5 := 
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub (bx_pre) (ax_pre))) ((fp32_sub (cy_pre) (ay_pre)))) ) ”
) \/
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub (bx_pre) (ax_pre))) ((fp32_sub (cy_pre) (ay_pre)))) ) ”
).

Definition point_cross_safety_wit_5_split_goal_1 := 
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub (bx_pre) (ax_pre))) ((fp32_sub (cy_pre) (ay_pre)))) ) ”
.

Definition point_cross_safety_wit_6 := 
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (cy_pre) (ay_pre)) ) ”
) \/
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (cy_pre) (ay_pre)) ) ”
).

Definition point_cross_safety_wit_6_split_goal_1 := 
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (cy_pre) (ay_pre)) ) ”
.

Definition point_cross_safety_wit_7 := 
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (bx_pre) (ax_pre)) ) ”
) \/
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (bx_pre) (ax_pre)) ) ”
).

Definition point_cross_safety_wit_7_split_goal_1 := 
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  ((( &( "ax" ) )) # Float  |-> ax_pre)
  **  ((( &( "ay" ) )) # Float  |-> ay_pre)
  **  ((( &( "bx" ) )) # Float  |-> bx_pre)
  **  ((( &( "b_y" ) )) # Float  |-> b_y_pre)
  **  ((( &( "cx" ) )) # Float  |-> cx_pre)
  **  ((( &( "cy" ) )) # Float  |-> cy_pre)
|--
  “ (fp32_isFinite (fp32_sub (bx_pre) (ax_pre)) ) ”
.

Definition point_cross_return_wit_1 := 
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_sub ((fp32_mul ((fp32_sub (bx_pre) (ax_pre))) ((fp32_sub (cy_pre) (ay_pre))))) ((fp32_mul ((fp32_sub (b_y_pre) (ay_pre))) ((fp32_sub (cx_pre) (ax_pre)))))) (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre))))) ”
  &&  emp
) \/
(
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  TT && emp 
|--
  “ (fp32_eq (fp32_sub ((fp32_mul ((fp32_sub (bx_pre) (ax_pre))) ((fp32_sub (cy_pre) (ay_pre))))) ((fp32_mul ((fp32_sub (b_y_pre) (ay_pre))) ((fp32_sub (cx_pre) (ax_pre)))))) (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre))))) ”
  &&  emp
).

Definition point_cross_return_wit_1_split_goal_1 := 
forall (cy_pre: fp32) (cx_pre: fp32) (b_y_pre: fp32) (bx_pre: fp32) (ay_pre: fp32) (ax_pre: fp32) (PreH1 : (fp32_isFinite (pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH2 : (fp32_isFinite (pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))) )) (PreH3 : (fp32_isFinite (pointf_get_x ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH4 : (fp32_isFinite (pointf_get_y ((pointf_mk (bx_pre) (b_y_pre)))) )) (PreH5 : (fp32_isFinite (pointf_get_x ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH6 : (fp32_isFinite (pointf_get_y ((pointf_mk (cx_pre) (cy_pre)))) )) (PreH7 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH8 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH9 : (fp32_isFinite (fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH10 : (fp32_isFinite (fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))) )) (PreH11 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_y ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH12 : (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((pointf_mk (bx_pre) (b_y_pre))))) ((pointf_get_y ((pointf_mk (ax_pre) (ay_pre))))))) ((fp32_sub ((pointf_get_x ((pointf_mk (cx_pre) (cy_pre))))) ((pointf_get_x ((pointf_mk (ax_pre) (ay_pre)))))))) )) (PreH13 : (fp32_isFinite (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))) )) ,
  (fp32_eq (fp32_sub ((fp32_mul ((fp32_sub (bx_pre) (ax_pre))) ((fp32_sub (cy_pre) (ay_pre))))) ((fp32_mul ((fp32_sub (b_y_pre) (ay_pre))) ((fp32_sub (cx_pre) (ax_pre)))))) (pointf_cross ((pointf_mk (ax_pre) (ay_pre))) ((pointf_mk (bx_pre) (b_y_pre))) ((pointf_mk (cx_pre) (cy_pre)))))
.

(*----- Function swap_points -----*)

Definition swap_points_return_wit_1 := 
(
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  (PointFArray.full pts_pre n_pre (replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre (replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre l __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))))) __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) ((replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre l __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))))))) )
|--
  (PointFArray.full pts_pre n_pre (pointf_swap (l) (i_pre) (j_pre)) )
) \/
(
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  TT && emp 
|--
  “ ((replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre (replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre l __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))))) __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) ((replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre l __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))))))) = (pointf_swap (l) (i_pre) (j_pre))) ”
  &&  emp
).

Definition swap_points_return_wit_1_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  ((replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre (replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre l __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))))) __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) ((replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre l __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))))))) = (pointf_swap (l) (i_pre) (j_pre)))
.

Definition swap_points_partial_solve_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  (PointFArray.full pts_pre n_pre l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i_pre l __default_PointF))))
  **  (PointFArray.missing_i pts_pre i_pre 0 n_pre l )
  **  ((&(((pts_pre + (i_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i_pre l __default_PointF))))
.

Definition swap_points_partial_solve_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  (PointFArray.full pts_pre n_pre l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i_pre l __default_PointF))))
  **  (PointFArray.missing_i pts_pre i_pre 0 n_pre l )
  **  ((&(((pts_pre + (i_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i_pre l __default_PointF))))
.

Definition swap_points_partial_solve_wit_3 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  (PointFArray.full pts_pre n_pre l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((&(((pts_pre + (j_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth j_pre l __default_PointF))))
  **  (PointFArray.missing_i pts_pre j_pre 0 n_pre l )
  **  ((&(((pts_pre + (j_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth j_pre l __default_PointF))))
.

Definition swap_points_partial_solve_wit_4 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  (PointFArray.full pts_pre n_pre l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |->_)
  **  (PointFArray.missing_i pts_pre i_pre 0 n_pre l )
  **  ((&(((pts_pre + (i_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i_pre l __default_PointF))))
.

Definition swap_points_partial_solve_wit_5 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  (PointFArray.full pts_pre n_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((&(((pts_pre + (j_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF))))
  **  (PointFArray.missing_i pts_pre j_pre 0 n_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) )
  **  ((&(((pts_pre + (j_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF))))
.

Definition swap_points_partial_solve_wit_6 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  (PointFArray.full pts_pre n_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((&(((pts_pre + (i_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |->_)
  **  (PointFArray.missing_i pts_pre i_pre 0 n_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) )
  **  ((&(((pts_pre + (i_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF))))
.

Definition swap_points_partial_solve_wit_7 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  (PointFArray.full pts_pre n_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((&(((pts_pre + (j_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |->_)
  **  (PointFArray.missing_i pts_pre j_pre 0 n_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) )
  **  ((&(((pts_pre + (j_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF))))
.

Definition swap_points_partial_solve_wit_8 := 
forall (j_pre: Z) (i_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((Zlength (l)) = n_pre)) ,
  (PointFArray.full pts_pre n_pre (replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre l __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))))) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n_pre) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((&(((pts_pre + (j_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |->_)
  **  (PointFArray.missing_i pts_pre j_pre 0 n_pre (replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre l __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))))) )
  **  ((&(((pts_pre + (j_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth j_pre (replace_Znth (j_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre l __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth i_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))) ((pointf_get_y ((Znth j_pre (replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)) __default_PointF)))))) ((replace_Znth (i_pre) ((pointf_mk ((pointf_get_x ((Znth j_pre l __default_PointF)))) ((pointf_get_y ((Znth i_pre l __default_PointF)))))) (l)))))) __default_PointF))))
.

(*----- Function partition_xy_points -----*)

Definition partition_xy_points_safety_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (PointFArray.full pts_pre n_pre l )
  **  ((( &( "pivot_y" ) )) # Float  |-> (pointf_get_y ((Znth high_pre l __default_PointF))))
  **  ((( &( "pivot_x" ) )) # Float  |-> (pointf_get_x ((Znth high_pre l __default_PointF))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
|--
  “ ((low_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low_pre - 1 )) ”
.

Definition partition_xy_points_safety_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (PointFArray.full pts_pre n_pre l )
  **  ((( &( "pivot_y" ) )) # Float  |-> (pointf_get_y ((Znth high_pre l __default_PointF))))
  **  ((( &( "pivot_x" ) )) # Float  |-> (pointf_get_x ((Znth high_pre l __default_PointF))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_xy_points_safety_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH2 : (j < high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |-> retval)
  **  (PointFArray.full pts_pre n_pre cur )
  **  ((( &( "ay" ) )) # Float  |-> (pointf_get_y ((Znth j cur __default_PointF))))
  **  ((( &( "ax" ) )) # Float  |-> (pointf_get_x ((Znth j cur __default_PointF))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition partition_xy_points_safety_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : (retval <= 0)) (PreH2 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (cur)) = n_pre)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH14 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH18 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |-> retval)
  **  (PointFArray.full pts_pre n_pre cur )
  **  ((( &( "ay" ) )) # Float  |-> (pointf_get_y ((Znth j cur __default_PointF))))
  **  ((( &( "ax" ) )) # Float  |-> (pointf_get_x ((Znth j cur __default_PointF))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_xy_points_safety_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre (pointf_swap (cur) ((i + 1 )) (j)) )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_xy_points_safety_wit_6 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_xy_points_safety_wit_7 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : (retval > 0)) (PreH2 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (cur)) = n_pre)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH14 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH18 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_xy_points_safety_wit_8 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : (j >= high_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (cur)) = n_pre)) (PreH11 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH17 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
  **  (PointFArray.full pts_pre n_pre cur )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_xy_points_entail_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  (PointFArray.full pts_pre n_pre l )
|--
  EX (cur: (@list PointF)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (low_pre - 1 )) ” 
  &&  “ ((low_pre - 1 ) < low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) (pointf_get_x ((Znth high_pre l __default_PointF)))) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) (pointf_get_y ((Znth high_pre l __default_PointF)))) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (cur)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (cur)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk ((pointf_get_x ((Znth high_pre l __default_PointF)))) ((pointf_get_y ((Znth high_pre l __default_PointF))))))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk ((pointf_get_x ((Znth high_pre l __default_PointF)))) ((pointf_get_y ((Znth high_pre l __default_PointF))))))) ) ” 
  &&  “ (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk ((pointf_get_x ((Znth high_pre l __default_PointF)))) ((pointf_get_y ((Znth high_pre l __default_PointF))))) (low_pre - 1 ) low_pre ) ”
  &&  (PointFArray.full pts_pre n_pre cur )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  TT && emp 
|--
  “ (pointf_xy_partition_scan_inv l l low_pre high_pre (pointf_mk ((pointf_get_x ((Znth high_pre l __default_PointF)))) ((pointf_get_y ((Znth high_pre l __default_PointF))))) (low_pre - 1 ) low_pre ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk ((pointf_get_x ((Znth high_pre l __default_PointF)))) ((pointf_get_y ((Znth high_pre l __default_PointF))))))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk ((pointf_get_x ((Znth high_pre l __default_PointF)))) ((pointf_get_y ((Znth high_pre l __default_PointF))))))) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_eq ((Znth high_pre l __default_PointF).(pointf_y) ) (pointf_get_y ((Znth high_pre l __default_PointF)))) ” 
  &&  “ (fp32_eq ((Znth high_pre l __default_PointF).(pointf_x) ) (pointf_get_x ((Znth high_pre l __default_PointF)))) ”
  &&  emp
).

Definition partition_xy_points_entail_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  (pointf_xy_partition_scan_inv l l low_pre high_pre (pointf_mk ((pointf_get_x ((Znth high_pre l __default_PointF)))) ((pointf_get_y ((Znth high_pre l __default_PointF))))) (low_pre - 1 ) low_pre )
.

Definition partition_xy_points_entail_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  (fp32_isFinite (pointf_get_y ((pointf_mk ((pointf_get_x ((Znth high_pre l __default_PointF)))) ((pointf_get_y ((Znth high_pre l __default_PointF))))))) )
.

Definition partition_xy_points_entail_wit_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  (fp32_isFinite (pointf_get_x ((pointf_mk ((pointf_get_x ((Znth high_pre l __default_PointF)))) ((pointf_get_y ((Znth high_pre l __default_PointF))))))) )
.

Definition partition_xy_points_entail_wit_1_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))
.

Definition partition_xy_points_entail_wit_1_split_goal_5 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  (fp32_eq ((Znth high_pre l __default_PointF).(pointf_y) ) (pointf_get_y ((Znth high_pre l __default_PointF))))
.

Definition partition_xy_points_entail_wit_1_split_goal_6 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  (fp32_eq ((Znth high_pre l __default_PointF).(pointf_x) ) (pointf_get_x ((Znth high_pre l __default_PointF))))
.

Definition partition_xy_points_entail_wit_2_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre (pointf_swap (cur_2) ((i + 1 )) (j)) )
|--
  EX (cur: (@list PointF)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (cur)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (cur)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointFArray.full pts_pre n_pre cur )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (pointf_xy_partition_scan_inv l (pointf_swap (cur_2) ((i + 1 )) (j)) low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) ((pointf_swap (cur_2) ((i + 1 )) (j)))) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) ((pointf_swap (cur_2) ((i + 1 )) (j)))) ) ” 
  &&  “ (fp32_eq ((Znth high_pre (pointf_swap (cur_2) ((i + 1 )) (j)) __default_PointF).(pointf_y) ) pivot_y) ” 
  &&  “ (fp32_eq ((Znth high_pre (pointf_swap (cur_2) ((i + 1 )) (j)) __default_PointF).(pointf_x) ) pivot_x) ” 
  &&  “ ((Zlength ((pointf_swap (cur_2) ((i + 1 )) (j)))) = n_pre) ”
  &&  emp
).

Definition partition_xy_points_entail_wit_2_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (pointf_xy_partition_scan_inv l (pointf_swap (cur_2) ((i + 1 )) (j)) low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) )
.

Definition partition_xy_points_entail_wit_2_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (Forall fp32_isFinite (map (pointf_get_y) ((pointf_swap (cur_2) ((i + 1 )) (j)))) )
.

Definition partition_xy_points_entail_wit_2_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (Forall fp32_isFinite (map (pointf_get_x) ((pointf_swap (cur_2) ((i + 1 )) (j)))) )
.

Definition partition_xy_points_entail_wit_2_1_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (fp32_eq ((Znth high_pre (pointf_swap (cur_2) ((i + 1 )) (j)) __default_PointF).(pointf_y) ) pivot_y)
.

Definition partition_xy_points_entail_wit_2_1_split_goal_5 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (fp32_eq ((Znth high_pre (pointf_swap (cur_2) ((i + 1 )) (j)) __default_PointF).(pointf_x) ) pivot_x)
.

Definition partition_xy_points_entail_wit_2_1_split_goal_6 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((Zlength ((pointf_swap (cur_2) ((i + 1 )) (j)))) = n_pre)
.

Definition partition_xy_points_entail_wit_2_2 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur_2 )
|--
  EX (cur: (@list PointF)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (cur)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (cur)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) (i + 1 ) (j + 1 ) ) ”
  &&  (PointFArray.full pts_pre n_pre cur )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) (i + 1 ) ((i + 1 ) + 1 ) ) ”
  &&  emp
).

Definition partition_xy_points_entail_wit_2_2_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) = j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur_2)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) (i + 1 ) ((i + 1 ) + 1 ) )
.

Definition partition_xy_points_entail_wit_2_3 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : (retval > 0)) (PreH2 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (cur_2)) = n_pre)) (PreH13 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH18 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur_2 )
|--
  EX (cur: (@list PointF)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (cur)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (cur)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i (j + 1 ) ) ”
  &&  (PointFArray.full pts_pre n_pre cur )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : (retval > 0)) (PreH2 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (cur_2)) = n_pre)) (PreH13 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH18 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i (j + 1 ) ) ”
  &&  emp
).

Definition partition_xy_points_entail_wit_2_3_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur_2: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : (retval > 0)) (PreH2 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur_2 __default_PointF)))) ((pointf_get_y ((Znth j cur_2 __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH3 : (j < high_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((low_pre - 1 ) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (cur_2)) = n_pre)) (PreH13 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_x) ) pivot_x)) (PreH14 : (fp32_eq ((Znth high_pre cur_2 __default_PointF).(pointf_y) ) pivot_y)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (cur_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (cur_2)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur_2 ) /\ (In pb cur_2 )) /\ (In pc cur_2 )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH18 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (pointf_xy_partition_scan_inv l cur_2 low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i (j + 1 ) )
.

Definition partition_xy_points_return_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre (pointf_swap (cur) ((i + 1 )) (high_pre)) )
|--
  EX (out: (@list PointF)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ (pointf_permutation l out ) ” 
  &&  “ (pointf_same_outside_range l out low_pre high_pre ) ” 
  &&  “ (pointf_xy_partitioned_at out low_pre high_pre (i + 1 ) ) ”
  &&  (PointFArray.full pts_pre n_pre out )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (pointf_xy_partitioned_at (pointf_swap (cur) ((i + 1 )) (high_pre)) low_pre high_pre (i + 1 ) ) ” 
  &&  “ (pointf_same_outside_range l (pointf_swap (cur) ((i + 1 )) (high_pre)) low_pre high_pre ) ” 
  &&  “ (pointf_permutation l (pointf_swap (cur) ((i + 1 )) (high_pre)) ) ”
  &&  emp
).

Definition partition_xy_points_return_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (pointf_xy_partitioned_at (pointf_swap (cur) ((i + 1 )) (high_pre)) low_pre high_pre (i + 1 ) )
.

Definition partition_xy_points_return_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (pointf_same_outside_range l (pointf_swap (cur) ((i + 1 )) (high_pre)) low_pre high_pre )
.

Definition partition_xy_points_return_wit_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (pointf_permutation l (pointf_swap (cur) ((i + 1 )) (high_pre)) )
.

Definition partition_xy_points_return_wit_2 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur )
|--
  EX (out: (@list PointF)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ (pointf_permutation l out ) ” 
  &&  “ (pointf_same_outside_range l out low_pre high_pre ) ” 
  &&  “ (pointf_xy_partitioned_at out low_pre high_pre (i + 1 ) ) ”
  &&  (PointFArray.full pts_pre n_pre out )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  TT && emp 
|--
  “ (pointf_xy_partitioned_at cur low_pre (i + 1 ) (i + 1 ) ) ” 
  &&  “ (pointf_same_outside_range l cur low_pre (i + 1 ) ) ” 
  &&  “ (pointf_permutation l cur ) ”
  &&  emp
).

Definition partition_xy_points_return_wit_2_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (pointf_xy_partitioned_at cur low_pre (i + 1 ) (i + 1 ) )
.

Definition partition_xy_points_return_wit_2_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (pointf_same_outside_range l cur low_pre (i + 1 ) )
.

Definition partition_xy_points_return_wit_2_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) = high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (pointf_permutation l cur )
.

Definition partition_xy_points_partial_solve_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre l )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (l)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (l)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
  &&  ((&(((pts_pre + (high_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth high_pre l __default_PointF))))
  **  (PointFArray.missing_i pts_pre high_pre 0 n_pre l )
  **  ((&(((pts_pre + (high_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth high_pre l __default_PointF))))
.

Definition partition_xy_points_partial_solve_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF))  __default_PointF (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH9 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre l )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (l)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (l)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
  &&  ((&(((pts_pre + (high_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth high_pre l __default_PointF))))
  **  (PointFArray.missing_i pts_pre high_pre 0 n_pre l )
  **  ((&(((pts_pre + (high_pre * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth high_pre l __default_PointF))))
.

Definition partition_xy_points_partial_solve_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : (j < high_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (cur)) = n_pre)) (PreH11 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH17 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur )
|--
  “ (j < high_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (cur)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (cur)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts_pre + (j * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth j cur __default_PointF))))
  **  (PointFArray.missing_i pts_pre j 0 n_pre cur )
  **  ((&(((pts_pre + (j * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth j cur __default_PointF))))
.

Definition partition_xy_points_partial_solve_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : (j < high_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (cur)) = n_pre)) (PreH11 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH17 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur )
|--
  “ (j < high_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (cur)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (cur)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j ) ”
  &&  ((&(((pts_pre + (j * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth j cur __default_PointF))))
  **  (PointFArray.missing_i pts_pre j 0 n_pre cur )
  **  ((&(((pts_pre + (j * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth j cur __default_PointF))))
.

Definition partition_xy_points_partial_solve_wit_5_pure := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : (j < high_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (cur)) = n_pre)) (PreH11 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH17 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (PointFArray.full pts_pre n_pre cur )
  **  ((( &( "ay" ) )) # Float  |-> (pointf_get_y ((Znth j cur __default_PointF))))
  **  ((( &( "ax" ) )) # Float  |-> (pointf_get_x ((Znth j cur __default_PointF))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF))))))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF))))))) ) ”
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (high_pre <= INT_MAX)) (PreH4 : (low_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (high_pre >= INT_MIN)) (PreH9 : (low_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (j < high_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= low_pre)) (PreH15 : (low_pre <= high_pre)) (PreH16 : (high_pre < n_pre)) (PreH17 : ((low_pre - 1 ) <= i)) (PreH18 : (i < j)) (PreH19 : (j <= high_pre)) (PreH20 : ((Zlength (cur)) = n_pre)) (PreH21 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH22 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH23 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH24 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH25 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH26 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH27 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH28 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (PointFArray.full pts_pre n_pre cur )
  **  ((( &( "ay" ) )) # Float  |-> (pointf_get_y ((Znth j cur __default_PointF))))
  **  ((( &( "ax" ) )) # Float  |-> (pointf_get_x ((Znth j cur __default_PointF))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ (fp32_isFinite (pointf_get_x ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF))))))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF))))))) ) ”
).

Definition partition_xy_points_partial_solve_wit_5_pure_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (high_pre <= INT_MAX)) (PreH4 : (low_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (high_pre >= INT_MIN)) (PreH9 : (low_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (j < high_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= low_pre)) (PreH15 : (low_pre <= high_pre)) (PreH16 : (high_pre < n_pre)) (PreH17 : ((low_pre - 1 ) <= i)) (PreH18 : (i < j)) (PreH19 : (j <= high_pre)) (PreH20 : ((Zlength (cur)) = n_pre)) (PreH21 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH22 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH23 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH24 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH25 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH26 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH27 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH28 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (PointFArray.full pts_pre n_pre cur )
  **  ((( &( "ay" ) )) # Float  |-> (pointf_get_y ((Znth j cur __default_PointF))))
  **  ((( &( "ax" ) )) # Float  |-> (pointf_get_x ((Znth j cur __default_PointF))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ (fp32_isFinite (pointf_get_x ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF))))))) ) ”
.

Definition partition_xy_points_partial_solve_wit_5_pure_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (high_pre <= INT_MAX)) (PreH4 : (low_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (j >= INT_MIN)) (PreH7 : (i >= INT_MIN)) (PreH8 : (high_pre >= INT_MIN)) (PreH9 : (low_pre >= INT_MIN)) (PreH10 : (n_pre >= INT_MIN)) (PreH11 : (j < high_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= low_pre)) (PreH15 : (low_pre <= high_pre)) (PreH16 : (high_pre < n_pre)) (PreH17 : ((low_pre - 1 ) <= i)) (PreH18 : (i < j)) (PreH19 : (j <= high_pre)) (PreH20 : ((Zlength (cur)) = n_pre)) (PreH21 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH22 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH23 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH24 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH25 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH26 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH27 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH28 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |->_)
  **  (PointFArray.full pts_pre n_pre cur )
  **  ((( &( "ay" ) )) # Float  |-> (pointf_get_y ((Znth j cur __default_PointF))))
  **  ((( &( "ax" ) )) # Float  |-> (pointf_get_x ((Znth j cur __default_PointF))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ (fp32_isFinite (pointf_get_y ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF))))))) ) ”
.

Definition partition_xy_points_partial_solve_wit_5_aux := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : (j < high_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (cur)) = n_pre)) (PreH11 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH17 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur )
|--
  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF))))))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF))))))) ) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (cur)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (cur)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointFArray.full pts_pre n_pre cur )
.

Definition partition_xy_points_partial_solve_wit_5 := partition_xy_points_partial_solve_wit_5_pure -> partition_xy_points_partial_solve_wit_5_aux.

Definition partition_xy_points_partial_solve_wit_6_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "c" ) )) # Int  |-> retval)
  **  (PointFArray.full pts_pre n_pre cur )
  **  ((( &( "ay" ) )) # Float  |-> (pointf_get_y ((Znth j cur __default_PointF))))
  **  ((( &( "ax" ) )) # Float  |-> (pointf_get_x ((Znth j cur __default_PointF))))
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ”
.

Definition partition_xy_points_partial_solve_wit_6_aux := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z) (retval: Z)  __default_PointF (PreH1 : ((i + 1 ) <> j)) (PreH2 : (retval <= 0)) (PreH3 : (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y)))))) (PreH4 : (j < high_pre)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : ((low_pre - 1 ) <= i)) (PreH11 : (i < j)) (PreH12 : (j <= high_pre)) (PreH13 : ((Zlength (cur)) = n_pre)) (PreH14 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH15 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH18 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH19 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH20 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH21 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> j) ” 
  &&  “ (retval <= 0) ” 
  &&  “ (retval = (pointf_cmp_xy ((pointf_mk ((pointf_get_x ((Znth j cur __default_PointF)))) ((pointf_get_y ((Znth j cur __default_PointF)))))) ((pointf_mk (pivot_x) (pivot_y))))) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (cur)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (cur)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointFArray.full pts_pre n_pre cur )
.

Definition partition_xy_points_partial_solve_wit_6 := partition_xy_points_partial_solve_wit_6_pure -> partition_xy_points_partial_solve_wit_6_aux.

Definition partition_xy_points_partial_solve_wit_7_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "pivot_x" ) )) # Float  |-> pivot_x)
  **  ((( &( "pivot_y" ) )) # Float  |-> pivot_y)
  **  (PointFArray.full pts_pre n_pre cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ”
.

Definition partition_xy_points_partial_solve_wit_7_aux := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (pivot_y: fp32) (pivot_x: fp32) (cur: (@list PointF)) (j: Z) (i: Z)  __default_PointF (PreH1 : ((i + 1 ) <> high_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (cur)) = n_pre)) (PreH12 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x)) (PreH13 : (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (cur)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (cur)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH17 : (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH18 : (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) )) (PreH19 : (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j )) ,
  (PointFArray.full pts_pre n_pre cur )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ ((i + 1 ) <> high_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ ((Zlength (cur)) = n_pre) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_x) ) pivot_x) ” 
  &&  “ (fp32_eq ((Znth high_pre cur __default_PointF).(pointf_y) ) pivot_y) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (cur)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (cur)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa cur ) /\ (In pb cur )) /\ (In pc cur )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (fp32_isFinite (pointf_get_x ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (fp32_isFinite (pointf_get_y ((pointf_mk (pivot_x) (pivot_y)))) ) ” 
  &&  “ (pointf_xy_partition_scan_inv l cur low_pre high_pre (pointf_mk (pivot_x) (pivot_y)) i j ) ”
  &&  (PointFArray.full pts_pre n_pre cur )
.

Definition partition_xy_points_partial_solve_wit_7 := partition_xy_points_partial_solve_wit_7_pure -> partition_xy_points_partial_solve_wit_7_aux.

(*----- Function quicksort_xy_points -----*)

Definition quicksort_xy_points_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (pointf_permutation l out )) (PreH5 : (pointf_same_outside_range l out left_pre right_pre )) (PreH6 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quicksort_xy_points_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (pointf_permutation l out )) (PreH5 : (pointf_same_outside_range l out left_pre right_pre )) (PreH6 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_xy_points_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (pointf_permutation l out )) (PreH6 : (pointf_same_outside_range l out left_pre right_pre )) (PreH7 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ False ”
.

Definition quicksort_xy_points_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (out_2: (@list PointF)) (PreH1 : (retval < right_pre)) (PreH2 : (pointf_permutation out out_2 )) (PreH3 : (pointf_same_outside_range out out_2 left_pre (retval - 1 ) )) (PreH4 : (pointf_xy_sorted_range out_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out )) (PreH9 : (pointf_same_outside_range l out left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_xy_points_safety_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (out_2: (@list PointF)) (PreH1 : (retval < right_pre)) (PreH2 : (pointf_permutation out out_2 )) (PreH3 : (pointf_same_outside_range out out_2 left_pre (retval - 1 ) )) (PreH4 : (pointf_xy_sorted_range out_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out )) (PreH9 : (pointf_same_outside_range l out left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_xy_points_safety_wit_6 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (pointf_permutation l out )) (PreH6 : (pointf_same_outside_range l out left_pre right_pre )) (PreH7 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_xy_points_safety_wit_7 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (pointf_permutation l out )) (PreH6 : (pointf_same_outside_range l out left_pre right_pre )) (PreH7 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_xy_points_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (out_4: (@list PointF)) (PreH1 : (pointf_permutation out_3 out_4 )) (PreH2 : (pointf_same_outside_range out_3 out_4 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (pointf_permutation out_2 out_3 )) (PreH6 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH7 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (pointf_permutation l out_2 )) (PreH12 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH13 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : (0 <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH22 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH23 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out_4 )
|--
  EX (out: (@list PointF)) ,
  “ (pointf_permutation l out ) ” 
  &&  “ (pointf_same_outside_range l out left_pre right_pre ) ” 
  &&  “ (pointf_xy_sorted_range out left_pre right_pre ) ”
  &&  (PointFArray.full pts_pre n_pre out )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (out_4: (@list PointF)) (PreH1 : (pointf_permutation out_3 out_4 )) (PreH2 : (pointf_same_outside_range out_3 out_4 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (pointf_permutation out_2 out_3 )) (PreH6 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH7 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (pointf_permutation l out_2 )) (PreH12 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH13 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : (0 <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH22 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH23 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  TT && emp 
|--
  “ (pointf_xy_sorted_range out_4 left_pre right_pre ) ” 
  &&  “ (pointf_same_outside_range l out_4 left_pre right_pre ) ” 
  &&  “ (pointf_permutation l out_4 ) ”
  &&  emp
).

Definition quicksort_xy_points_return_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (out_4: (@list PointF)) (PreH1 : (pointf_permutation out_3 out_4 )) (PreH2 : (pointf_same_outside_range out_3 out_4 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (pointf_permutation out_2 out_3 )) (PreH6 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH7 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (pointf_permutation l out_2 )) (PreH12 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH13 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : (0 <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH22 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH23 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_xy_sorted_range out_4 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (out_4: (@list PointF)) (PreH1 : (pointf_permutation out_3 out_4 )) (PreH2 : (pointf_same_outside_range out_3 out_4 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (pointf_permutation out_2 out_3 )) (PreH6 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH7 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (pointf_permutation l out_2 )) (PreH12 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH13 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : (0 <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH22 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH23 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_same_outside_range l out_4 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_1_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (out_4: (@list PointF)) (PreH1 : (pointf_permutation out_3 out_4 )) (PreH2 : (pointf_same_outside_range out_3 out_4 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (pointf_permutation out_2 out_3 )) (PreH6 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH7 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (pointf_permutation l out_2 )) (PreH12 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH13 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 50000)) (PreH17 : (0 <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH22 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH23 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_permutation l out_4 )
.

Definition quicksort_xy_points_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (pointf_permutation out_2 out_3 )) (PreH2 : (pointf_same_outside_range out_2 out_3 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out_3 )
|--
  EX (out: (@list PointF)) ,
  “ (pointf_permutation l out ) ” 
  &&  “ (pointf_same_outside_range l out left_pre right_pre ) ” 
  &&  “ (pointf_xy_sorted_range out left_pre right_pre ) ”
  &&  (PointFArray.full pts_pre n_pre out )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (pointf_permutation out_2 out_3 )) (PreH2 : (pointf_same_outside_range out_2 out_3 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  TT && emp 
|--
  “ (pointf_xy_sorted_range out_3 left_pre right_pre ) ” 
  &&  “ (pointf_same_outside_range l out_3 left_pre right_pre ) ” 
  &&  “ (pointf_permutation l out_3 ) ”
  &&  emp
).

Definition quicksort_xy_points_return_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (pointf_permutation out_2 out_3 )) (PreH2 : (pointf_same_outside_range out_2 out_3 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_xy_sorted_range out_3 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_2_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (pointf_permutation out_2 out_3 )) (PreH2 : (pointf_same_outside_range out_2 out_3 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_same_outside_range l out_3 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_2_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (pointf_permutation out_2 out_3 )) (PreH2 : (pointf_same_outside_range out_2 out_3 (retval + 1 ) right_pre )) (PreH3 : (pointf_xy_sorted_range out_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_permutation l out_3 )
.

Definition quicksort_xy_points_return_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (retval >= right_pre)) (PreH2 : (pointf_permutation out_2 out_3 )) (PreH3 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH4 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out_3 )
|--
  EX (out: (@list PointF)) ,
  “ (pointf_permutation l out ) ” 
  &&  “ (pointf_same_outside_range l out left_pre right_pre ) ” 
  &&  “ (pointf_xy_sorted_range out left_pre right_pre ) ”
  &&  (PointFArray.full pts_pre n_pre out )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (retval >= right_pre)) (PreH2 : (pointf_permutation out_2 out_3 )) (PreH3 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH4 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  TT && emp 
|--
  “ (pointf_xy_sorted_range out_3 left_pre right_pre ) ” 
  &&  “ (pointf_same_outside_range l out_3 left_pre right_pre ) ” 
  &&  “ (pointf_permutation l out_3 ) ”
  &&  emp
).

Definition quicksort_xy_points_return_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (retval >= right_pre)) (PreH2 : (pointf_permutation out_2 out_3 )) (PreH3 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH4 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_xy_sorted_range out_3 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_3_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (retval >= right_pre)) (PreH2 : (pointf_permutation out_2 out_3 )) (PreH3 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH4 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_same_outside_range l out_3 left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_3_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out_3: (@list PointF)) (PreH1 : (retval >= right_pre)) (PreH2 : (pointf_permutation out_2 out_3 )) (PreH3 : (pointf_same_outside_range out_2 out_3 left_pre (retval - 1 ) )) (PreH4 : (pointf_xy_sorted_range out_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_permutation l out_3 )
.

Definition quicksort_xy_points_return_wit_4 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH10 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre l )
|--
  EX (out: (@list PointF)) ,
  “ (pointf_permutation l out ) ” 
  &&  “ (pointf_same_outside_range l out left_pre right_pre ) ” 
  &&  “ (pointf_xy_sorted_range out left_pre right_pre ) ”
  &&  (PointFArray.full pts_pre n_pre out )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH10 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  TT && emp 
|--
  “ (pointf_xy_sorted_range l left_pre right_pre ) ” 
  &&  “ (pointf_same_outside_range l l left_pre right_pre ) ” 
  &&  “ (pointf_permutation l l ) ”
  &&  emp
).

Definition quicksort_xy_points_return_wit_4_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH10 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_xy_sorted_range l left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_4_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH10 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_same_outside_range l l left_pre right_pre )
.

Definition quicksort_xy_points_return_wit_4_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list PointF)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH10 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (pointf_permutation l l )
.

Definition quicksort_xy_points_partial_solve_wit_1_pure := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH10 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (PointFArray.full pts_pre n_pre l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (l)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (l)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (right_pre >= INT_MIN)) (PreH5 : (left_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH16 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (PointFArray.full pts_pre n_pre l )
|--
  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
).

Definition quicksort_xy_points_partial_solve_wit_1_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (right_pre >= INT_MIN)) (PreH5 : (left_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH16 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (PointFArray.full pts_pre n_pre l )
|--
  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
.

Definition quicksort_xy_points_partial_solve_wit_1_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH10 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) ,
  (PointFArray.full pts_pre n_pre l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (l)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (l)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (l)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (l)) ) ” 
  &&  “ forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 l ) /\ (In pb_2 l )) /\ (In pc_2 l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) ))) ”
  &&  (PointFArray.full pts_pre n_pre l )
.

Definition quicksort_xy_points_partial_solve_wit_1 := quicksort_xy_points_partial_solve_wit_1_pure -> quicksort_xy_points_partial_solve_wit_1_aux.

Definition quicksort_xy_points_partial_solve_wit_2_pure := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (pointf_permutation l out )) (PreH5 : (pointf_same_outside_range l out left_pre right_pre )) (PreH6 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ ((Zlength (out)) = n_pre) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (pointf_permutation l out )) (PreH13 : (pointf_same_outside_range l out left_pre right_pre )) (PreH14 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH23 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH24 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (out)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ”
).

Definition quicksort_xy_points_partial_solve_wit_2_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (pointf_permutation l out )) (PreH13 : (pointf_same_outside_range l out left_pre right_pre )) (PreH14 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH23 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH24 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (out)) = n_pre) ”
.

Definition quicksort_xy_points_partial_solve_wit_2_pure_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (pointf_permutation l out )) (PreH13 : (pointf_same_outside_range l out left_pre right_pre )) (PreH14 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH23 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH24 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ”
.

Definition quicksort_xy_points_partial_solve_wit_2_pure_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (pointf_permutation l out )) (PreH13 : (pointf_same_outside_range l out left_pre right_pre )) (PreH14 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : ((-1) <= right_pre)) (PreH20 : (right_pre < n_pre)) (PreH21 : ((Zlength (l)) = n_pre)) (PreH22 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH23 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH24 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ”
.

Definition quicksort_xy_points_partial_solve_wit_2_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (pointf_permutation l out )) (PreH5 : (pointf_same_outside_range l out left_pre right_pre )) (PreH6 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : ((Zlength (l)) = n_pre)) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH16 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ ((Zlength (out)) = n_pre) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (pointf_permutation l out ) ” 
  &&  “ (pointf_same_outside_range l out left_pre right_pre ) ” 
  &&  “ (pointf_xy_partitioned_at out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (l)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (l)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
  &&  (PointFArray.full pts_pre n_pre out )
.

Definition quicksort_xy_points_partial_solve_wit_2 := quicksort_xy_points_partial_solve_wit_2_pure -> quicksort_xy_points_partial_solve_wit_2_aux.

Definition quicksort_xy_points_partial_solve_wit_3_pure := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out: (@list PointF)) (PreH1 : (retval < right_pre)) (PreH2 : (pointf_permutation out_2 out )) (PreH3 : (pointf_same_outside_range out_2 out left_pre (retval - 1 ) )) (PreH4 : (pointf_xy_sorted_range out left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ ((Zlength (out)) = n_pre) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out: (@list PointF)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (pointf_permutation out_2 out )) (PreH11 : (pointf_same_outside_range out_2 out left_pre (retval - 1 ) )) (PreH12 : (pointf_xy_sorted_range out left_pre (retval - 1 ) )) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (pointf_permutation l out_2 )) (PreH17 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH18 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH27 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH28 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (out)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ”
).

Definition quicksort_xy_points_partial_solve_wit_3_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out: (@list PointF)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (pointf_permutation out_2 out )) (PreH11 : (pointf_same_outside_range out_2 out left_pre (retval - 1 ) )) (PreH12 : (pointf_xy_sorted_range out left_pre (retval - 1 ) )) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (pointf_permutation l out_2 )) (PreH17 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH18 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH27 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH28 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (out)) = n_pre) ”
.

Definition quicksort_xy_points_partial_solve_wit_3_pure_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out: (@list PointF)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (pointf_permutation out_2 out )) (PreH11 : (pointf_same_outside_range out_2 out left_pre (retval - 1 ) )) (PreH12 : (pointf_xy_sorted_range out left_pre (retval - 1 ) )) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (pointf_permutation l out_2 )) (PreH17 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH18 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH27 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH28 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ”
.

Definition quicksort_xy_points_partial_solve_wit_3_pure_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out: (@list PointF)) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (pointf_permutation out_2 out )) (PreH11 : (pointf_same_outside_range out_2 out left_pre (retval - 1 ) )) (PreH12 : (pointf_xy_sorted_range out left_pre (retval - 1 ) )) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (pointf_permutation l out_2 )) (PreH17 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH18 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : (0 <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : (0 <= left_pre)) (PreH23 : ((-1) <= right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : ((Zlength (l)) = n_pre)) (PreH26 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH27 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH28 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ”
.

Definition quicksort_xy_points_partial_solve_wit_3_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out_2: (@list PointF)) (retval: Z) (out: (@list PointF)) (PreH1 : (retval < right_pre)) (PreH2 : (pointf_permutation out_2 out )) (PreH3 : (pointf_same_outside_range out_2 out left_pre (retval - 1 ) )) (PreH4 : (pointf_xy_sorted_range out left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (pointf_permutation l out_2 )) (PreH9 : (pointf_same_outside_range l out_2 left_pre right_pre )) (PreH10 : (pointf_xy_partitioned_at out_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (n_pre <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH20 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ ((Zlength (out)) = n_pre) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (pointf_permutation out_2 out ) ” 
  &&  “ (pointf_same_outside_range out_2 out left_pre (retval - 1 ) ) ” 
  &&  “ (pointf_xy_sorted_range out left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (pointf_permutation l out_2 ) ” 
  &&  “ (pointf_same_outside_range l out_2 left_pre right_pre ) ” 
  &&  “ (pointf_xy_partitioned_at out_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (l)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (l)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
  &&  (PointFArray.full pts_pre n_pre out )
.

Definition quicksort_xy_points_partial_solve_wit_3 := quicksort_xy_points_partial_solve_wit_3_pure -> quicksort_xy_points_partial_solve_wit_3_aux.

Definition quicksort_xy_points_partial_solve_wit_4_pure := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (pointf_permutation l out )) (PreH6 : (pointf_same_outside_range l out left_pre right_pre )) (PreH7 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ ((Zlength (out)) = n_pre) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (retval <= left_pre)) (PreH11 : (left_pre <= retval)) (PreH12 : (retval <= right_pre)) (PreH13 : (pointf_permutation l out )) (PreH14 : (pointf_same_outside_range l out left_pre right_pre )) (PreH15 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH16 : (left_pre < right_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 50000)) (PreH19 : (0 <= left_pre)) (PreH20 : ((-1) <= right_pre)) (PreH21 : (right_pre < n_pre)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH24 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH25 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (out)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ”
).

Definition quicksort_xy_points_partial_solve_wit_4_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (retval <= left_pre)) (PreH11 : (left_pre <= retval)) (PreH12 : (retval <= right_pre)) (PreH13 : (pointf_permutation l out )) (PreH14 : (pointf_same_outside_range l out left_pre right_pre )) (PreH15 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH16 : (left_pre < right_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 50000)) (PreH19 : (0 <= left_pre)) (PreH20 : ((-1) <= right_pre)) (PreH21 : (right_pre < n_pre)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH24 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH25 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((Zlength (out)) = n_pre) ”
.

Definition quicksort_xy_points_partial_solve_wit_4_pure_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (retval <= left_pre)) (PreH11 : (left_pre <= retval)) (PreH12 : (retval <= right_pre)) (PreH13 : (pointf_permutation l out )) (PreH14 : (pointf_same_outside_range l out left_pre right_pre )) (PreH15 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH16 : (left_pre < right_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 50000)) (PreH19 : (0 <= left_pre)) (PreH20 : ((-1) <= right_pre)) (PreH21 : (right_pre < n_pre)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH24 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH25 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ”
.

Definition quicksort_xy_points_partial_solve_wit_4_pure_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (right_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (right_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (n_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (retval <= left_pre)) (PreH11 : (left_pre <= retval)) (PreH12 : (retval <= right_pre)) (PreH13 : (pointf_permutation l out )) (PreH14 : (pointf_same_outside_range l out left_pre right_pre )) (PreH15 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH16 : (left_pre < right_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 50000)) (PreH19 : (0 <= left_pre)) (PreH20 : ((-1) <= right_pre)) (PreH21 : (right_pre < n_pre)) (PreH22 : ((Zlength (l)) = n_pre)) (PreH23 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH24 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH25 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ”
.

Definition quicksort_xy_points_partial_solve_wit_4_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (pts_pre: Z) (l: (@list PointF)) (out: (@list PointF)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (pointf_permutation l out )) (PreH6 : (pointf_same_outside_range l out left_pre right_pre )) (PreH7 : (pointf_xy_partitioned_at out left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : ((-1) <= right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : ((Zlength (l)) = n_pre)) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (l)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (l)) )) (PreH17 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) ,
  (PointFArray.full pts_pre n_pre out )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ ((Zlength (out)) = n_pre) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (pointf_permutation l out ) ” 
  &&  “ (pointf_same_outside_range l out left_pre right_pre ) ” 
  &&  “ (pointf_xy_partitioned_at out left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (l)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (l)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa l ) /\ (In pb l )) /\ (In pc l )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
  &&  (PointFArray.full pts_pre n_pre out )
.

Definition quicksort_xy_points_partial_solve_wit_4 := quicksort_xy_points_partial_solve_wit_4_pure -> quicksort_xy_points_partial_solve_wit_4_aux.

(*----- Function andrew_build_from_sorted -----*)

Definition andrew_build_from_sorted_safety_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (sorted: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH6 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH7 : (pointf_xy_sorted sorted )) (PreH8 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition andrew_build_from_sorted_safety_wit_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (sorted: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH6 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH7 : (pointf_xy_sorted sorted )) (PreH8 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition andrew_build_from_sorted_safety_wit_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : (0 <= i)) (PreH4 : (i < n_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= i)) (PreH7 : ((Zlength (sorted)) = n_pre)) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH10 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH11 : (pointf_xy_sorted sorted )) (PreH12 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH15 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_4 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0)) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0)) ) ”
).

Definition andrew_build_from_sorted_safety_wit_4_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_4_split_goal_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_of_real (0.0)) ) ”
.

Definition andrew_build_from_sorted_safety_wit_5 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_5_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_6 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_6_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_7 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_7_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_8 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_9 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_9_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_10 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_11 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_12 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_12_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_13 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_13_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_14 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_15 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_15_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_16 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_17 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_18 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition andrew_build_from_sorted_safety_wit_19 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_20 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_21 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition andrew_build_from_sorted_safety_wit_22 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_23 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_24 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_le (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_25 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_26 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_27 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_28 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_29 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_scan_inv sorted (sublist (0) (k) (hull_all)) i k )) (PreH17 : ((n_pre <= i) -> (2 <= k))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lower_n" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ ((n_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_30 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_scan_inv sorted (sublist (0) (k) (hull_all)) i k )) (PreH17 : ((n_pre <= i) -> (2 <= k))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "lower_n" ) )) # Int  |-> k)
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_31 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : (0 <= (i + 1 ))) (PreH4 : ((i + 1 ) <= (n_pre - 1 ))) (PreH5 : (2 <= lower_n)) (PreH6 : (lower_n <= k)) (PreH7 : (k <= (2 * n_pre ))) (PreH8 : (lower_n = (Zlength (lower)))) (PreH9 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH10 : ((Zlength (sorted)) = n_pre)) (PreH11 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH12 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH13 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH14 : (pointf_xy_sorted sorted )) (PreH15 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH16 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH17 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH18 : (pointf_upper_scan_inv sorted lower (sublist (0) (k) (hull_all)) (i + 1 ) k lower_n )) (PreH19 : (lower_n <= n_pre)) (PreH20 : (k <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH21 : ((1 <= (i + 1 )) -> (k < (2 * n_pre )))) (PreH22 : (((i + 1 ) <= 0) -> (lower_n < k))) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition andrew_build_from_sorted_safety_wit_32 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0)) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ” 
  &&  “ (fp32_isFinite (fp32_of_real (0.0)) ) ”
).

Definition andrew_build_from_sorted_safety_wit_32_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_32_split_goal_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_of_real (0.0)) ) ”
.

Definition andrew_build_from_sorted_safety_wit_33 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_33_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_34 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_34_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_35 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_35_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_36 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_37 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_37_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_38 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_39 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_40 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_40_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_41 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_41_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_42 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_43 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
).

Definition andrew_build_from_sorted_safety_wit_43_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_isFinite (fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))) ) ”
.

Definition andrew_build_from_sorted_safety_wit_44 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ ((k - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 2 )) ”
.

Definition andrew_build_from_sorted_safety_wit_45 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_46 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition andrew_build_from_sorted_safety_wit_47 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_48 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_49 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition andrew_build_from_sorted_safety_wit_50 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_51 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition andrew_build_from_sorted_safety_wit_52 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_le (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower)))) (PreH11 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH20 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_53 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_54 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower)))) (PreH11 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH20 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_55 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_56 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower)))) (PreH11 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH20 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition andrew_build_from_sorted_safety_wit_57 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= (i + 1 ))) (PreH5 : ((i + 1 ) <= (n_pre - 1 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k <= (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_scan_inv sorted lower (sublist (0) (k) (hull_all)) (i + 1 ) k lower_n )) (PreH20 : (lower_n <= n_pre)) (PreH21 : (k <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH22 : ((1 <= (i + 1 )) -> (k < (2 * n_pre )))) (PreH23 : (((i + 1 ) <= 0) -> (lower_n < k))) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "lower_n" ) )) # Int  |-> lower_n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition andrew_build_from_sorted_entail_wit_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (sorted: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH6 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH7 : (pointf_xy_sorted sorted )) (PreH8 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  EX (hull_all: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_scan_inv sorted (sublist (0) (0) (hull_all)) 0 0 ) ” 
  &&  “ ((n_pre <= 0) -> (2 <= 0)) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (hull_init: (@list PointF)) (sorted: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH6 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH7 : (pointf_xy_sorted sorted )) (PreH8 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  TT && emp 
|--
  “ (pointf_lower_scan_inv sorted (sublist (0) (0) (hull_init)) 0 0 ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (hull_init: (@list PointF)) (sorted: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH6 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH7 : (pointf_xy_sorted sorted )) (PreH8 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (pointf_lower_scan_inv sorted (sublist (0) (0) (hull_init)) 0 0 )
.

Definition andrew_build_from_sorted_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (hull_init: (@list PointF)) (sorted: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH6 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH7 : (pointf_xy_sorted sorted )) (PreH8 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))
.

Definition andrew_build_from_sorted_entail_wit_2 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_scan_inv sorted (sublist (0) (k) (hull_all_2)) i k )) (PreH17 : ((n_pre <= i) -> (2 <= k))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all_2 )
|--
  EX (before: (@list PointF))  (hull_all: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_scan_inv sorted (sublist (0) (k) (hull_all_2)) i k )) (PreH17 : ((n_pre <= i) -> (2 <= k))) ,
  TT && emp 
|--
  EX (before: (@list PointF)) ,
  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k ) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_3 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before_2: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_le (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH17 : (pointf_lower_pop_inv sorted before_2 (sublist (0) (k) (hull_all_2)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all_2 )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  EX (before: (@list PointF))  (hull_all: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (k - 1 )) ” 
  &&  “ ((k - 1 ) <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) ((k - 1 )) (hull_all)) i (k - 1 ) ) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (before_2: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_le (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH17 : (pointf_lower_pop_inv sorted before_2 (sublist (0) (k) (hull_all_2)) i k )) ,
  TT && emp 
|--
  EX (before: (@list PointF)) ,
  “ (0 <= (k - 1 )) ” 
  &&  “ ((k - 1 ) <= i) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) ((k - 1 )) (hull_all_2)) i (k - 1 ) ) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_4_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  EX (hull_all: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (i + 1 )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_scan_inv sorted (sublist (0) ((k + 1 )) (hull_all)) (i + 1 ) (k + 1 ) ) ” 
  &&  “ ((n_pre <= (i + 1 )) -> (2 <= (k + 1 ))) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  TT && emp 
|--
  “ ((n_pre <= (i + 1 )) -> (2 <= (k + 1 ))) ” 
  &&  “ (pointf_lower_scan_inv sorted (sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) (i + 1 ) (k + 1 ) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ) ” 
  &&  “ ((Zlength ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) = (2 * n_pre )) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_4_1_split_goal_1 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  ((n_pre <= (i + 1 )) -> (2 <= (k + 1 )))
.

Definition andrew_build_from_sorted_entail_wit_4_1_split_goal_2 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  (pointf_lower_scan_inv sorted (sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) (i + 1 ) (k + 1 ) )
.

Definition andrew_build_from_sorted_entail_wit_4_1_split_goal_3 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  (Forall fp32_isFinite (map (pointf_get_y) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) )
.

Definition andrew_build_from_sorted_entail_wit_4_1_split_goal_4 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  (Forall fp32_isFinite (map (pointf_get_x) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) )
.

Definition andrew_build_from_sorted_entail_wit_4_1_split_goal_5 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  ((Zlength ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) = (2 * n_pre ))
.

Definition andrew_build_from_sorted_entail_wit_4_1_split_goal_6 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z) (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))
.

Definition andrew_build_from_sorted_entail_wit_4_2 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  EX (hull_all: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (i + 1 )) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_scan_inv sorted (sublist (0) ((k + 1 )) (hull_all)) (i + 1 ) (k + 1 ) ) ” 
  &&  “ ((n_pre <= (i + 1 )) -> (2 <= (k + 1 ))) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  TT && emp 
|--
  “ (pointf_lower_scan_inv sorted (sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) (i + 1 ) (k + 1 ) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ) ” 
  &&  “ ((Zlength ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) = (2 * n_pre )) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_4_2_split_goal_1 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  (pointf_lower_scan_inv sorted (sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) (i + 1 ) (k + 1 ) )
.

Definition andrew_build_from_sorted_entail_wit_4_2_split_goal_2 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  (Forall fp32_isFinite (map (pointf_get_y) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) )
.

Definition andrew_build_from_sorted_entail_wit_4_2_split_goal_3 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  (Forall fp32_isFinite (map (pointf_get_x) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) )
.

Definition andrew_build_from_sorted_entail_wit_4_2_split_goal_4 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  ((Zlength ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) = (2 * n_pre ))
.

Definition andrew_build_from_sorted_entail_wit_4_2_split_goal_5 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all_2)) i k )) ,
  forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))
.

Definition andrew_build_from_sorted_entail_wit_5 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_scan_inv sorted (sublist (0) (k) (hull_all_2)) i k )) (PreH17 : ((n_pre <= i) -> (2 <= k))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all_2 )
|--
  EX (hull_all: (@list PointF))  (lower: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= ((n_pre - 2 ) + 1 )) ” 
  &&  “ (((n_pre - 2 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (2 <= k) ” 
  &&  “ (k <= k) ” 
  &&  “ (k <= (2 * n_pre )) ” 
  &&  “ (k = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (k) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_scan_inv sorted lower (sublist (0) (k) (hull_all)) ((n_pre - 2 ) + 1 ) k k ) ” 
  &&  “ (k <= n_pre) ” 
  &&  “ (k <= (k + (n_pre - ((n_pre - 2 ) + 1 ) ) )) ” 
  &&  “ ((1 <= ((n_pre - 2 ) + 1 )) -> (k < (2 * n_pre ))) ” 
  &&  “ ((((n_pre - 2 ) + 1 ) <= 0) -> (k < k)) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_scan_inv sorted (sublist (0) (k) (hull_all_2)) i k )) (PreH17 : ((n_pre <= i) -> (2 <= k))) ,
  TT && emp 
|--
  “ (pointf_upper_scan_inv sorted (sublist (0) (k) ((sublist (0) (k) (hull_all_2)))) (sublist (0) (k) (hull_all_2)) ((n_pre - 2 ) + 1 ) k k ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (k = (Zlength ((sublist (0) (k) ((sublist (0) (k) (hull_all_2))))))) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_5_split_goal_1 := 
forall (n_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_scan_inv sorted (sublist (0) (k) (hull_all_2)) i k )) (PreH17 : ((n_pre <= i) -> (2 <= k))) ,
  (pointf_upper_scan_inv sorted (sublist (0) (k) ((sublist (0) (k) (hull_all_2)))) (sublist (0) (k) (hull_all_2)) ((n_pre - 2 ) + 1 ) k k )
.

Definition andrew_build_from_sorted_entail_wit_5_split_goal_2 := 
forall (n_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_scan_inv sorted (sublist (0) (k) (hull_all_2)) i k )) (PreH17 : ((n_pre <= i) -> (2 <= k))) ,
  forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))
.

Definition andrew_build_from_sorted_entail_wit_5_split_goal_3 := 
forall (n_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (k: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH16 : (pointf_lower_scan_inv sorted (sublist (0) (k) (hull_all_2)) i k )) (PreH17 : ((n_pre <= i) -> (2 <= k))) ,
  (k = (Zlength ((sublist (0) (k) ((sublist (0) (k) (hull_all_2)))))))
.

Definition andrew_build_from_sorted_entail_wit_6 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= (i + 1 ))) (PreH5 : ((i + 1 ) <= (n_pre - 1 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k <= (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_scan_inv sorted lower_2 (sublist (0) (k) (hull_all_2)) (i + 1 ) k lower_n )) (PreH20 : (lower_n <= n_pre)) (PreH21 : (k <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH22 : ((1 <= (i + 1 )) -> (k < (2 * n_pre )))) (PreH23 : (((i + 1 ) <= 0) -> (lower_n < k))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all_2 )
|--
  EX (before: (@list PointF))  (hull_all: (@list PointF))  (lower: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= (i + 1 ))) (PreH5 : ((i + 1 ) <= (n_pre - 1 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k <= (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_scan_inv sorted lower_2 (sublist (0) (k) (hull_all_2)) (i + 1 ) k lower_n )) (PreH20 : (lower_n <= n_pre)) (PreH21 : (k <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH22 : ((1 <= (i + 1 )) -> (k < (2 * n_pre )))) (PreH23 : (((i + 1 ) <= 0) -> (lower_n < k))) ,
  TT && emp 
|--
  EX (before: (@list PointF)) ,
  “ (0 <= i) ” 
  &&  “ (i <= ((Zlength (sorted)) - 2 )) ” 
  &&  “ (k < (2 * (Zlength (sorted)) )) ” 
  &&  “ ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2))))))) ((sublist (0) (k) (hull_all_2))))))) ” 
  &&  “ (pointf_upper_pop_inv sorted (sublist (0) ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2))))))) ((sublist (0) (k) (hull_all_2)))) before (sublist (0) (k) (hull_all_2)) i k (Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) ) ” 
  &&  “ ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) <= (Zlength (before))) ” 
  &&  “ ((Zlength (before)) <= ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) + ((Zlength (sorted)) - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * (Zlength (sorted)) ))) ” 
  &&  “ (((i + 1 ) <= 0) -> ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) < (Zlength (before)))) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_7 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before_2: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_le (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before_2 (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before_2)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before_2)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before_2)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before_2))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all_2 )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  EX (before: (@list PointF))  (hull_all: (@list PointF))  (lower: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= (k - 1 )) ” 
  &&  “ ((k - 1 ) < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) ((k - 1 )) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) ((k - 1 )) (hull_all)) i (k - 1 ) lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (before_2: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_le (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before_2 (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before_2)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before_2)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before_2)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before_2))))) ,
  TT && emp 
|--
  EX (before: (@list PointF)) ,
  “ ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) <= (k - 1 )) ” 
  &&  “ ((k - 1 ) < (2 * (Zlength (sorted)) )) ” 
  &&  “ ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) = (Zlength ((sublist (0) ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2))))))) ((sublist (0) ((k - 1 )) (hull_all_2))))))) ” 
  &&  “ (pointf_upper_pop_inv sorted (sublist (0) ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2))))))) ((sublist (0) ((k - 1 )) (hull_all_2)))) before (sublist (0) ((k - 1 )) (hull_all_2)) i (k - 1 ) (Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) ) ” 
  &&  “ ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) <= (Zlength (before))) ” 
  &&  “ ((Zlength (before)) <= ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) + ((Zlength (sorted)) - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * (Zlength (sorted)) ))) ” 
  &&  “ (((i + 1 ) <= 0) -> ((Zlength ((sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) < (Zlength (before)))) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_8_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  EX (hull_all: (@list PointF))  (lower: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) ((k + 1 )) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_scan_inv sorted lower (sublist (0) ((k + 1 )) (hull_all)) ((i - 1 ) + 1 ) (k + 1 ) lower_n ) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((k + 1 ) <= (lower_n + (n_pre - ((i - 1 ) + 1 ) ) )) ” 
  &&  “ ((1 <= ((i - 1 ) + 1 )) -> ((k + 1 ) < (2 * n_pre ))) ” 
  &&  “ ((((i - 1 ) + 1 ) <= 0) -> (lower_n < (k + 1 ))) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  TT && emp 
|--
  “ (pointf_upper_scan_inv sorted (sublist (0) (lower_n) ((sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))))) (sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ((i - 1 ) + 1 ) (k + 1 ) lower_n ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ) ” 
  &&  “ ((Zlength ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) = (2 * n_pre )) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (lower_n = (Zlength ((sublist (0) (lower_n) ((sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2))))))))))) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_8_1_split_goal_1 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (pointf_upper_scan_inv sorted (sublist (0) (lower_n) ((sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))))) (sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ((i - 1 ) + 1 ) (k + 1 ) lower_n )
.

Definition andrew_build_from_sorted_entail_wit_8_1_split_goal_2 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (Forall fp32_isFinite (map (pointf_get_y) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) )
.

Definition andrew_build_from_sorted_entail_wit_8_1_split_goal_3 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (Forall fp32_isFinite (map (pointf_get_x) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) )
.

Definition andrew_build_from_sorted_entail_wit_8_1_split_goal_4 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  ((Zlength ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) = (2 * n_pre ))
.

Definition andrew_build_from_sorted_entail_wit_8_1_split_goal_5 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))
.

Definition andrew_build_from_sorted_entail_wit_8_1_split_goal_6 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower_2)))) (PreH10 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (lower_n = (Zlength ((sublist (0) (lower_n) ((sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))))))))
.

Definition andrew_build_from_sorted_entail_wit_8_2 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))) )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  EX (hull_all: (@list PointF))  (lower: (@list PointF)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) ((k + 1 )) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_scan_inv sorted lower (sublist (0) ((k + 1 )) (hull_all)) ((i - 1 ) + 1 ) (k + 1 ) lower_n ) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((k + 1 ) <= (lower_n + (n_pre - ((i - 1 ) + 1 ) ) )) ” 
  &&  “ ((1 <= ((i - 1 ) + 1 )) -> ((k + 1 ) < (2 * n_pre ))) ” 
  &&  “ ((((i - 1 ) + 1 ) <= 0) -> (lower_n < (k + 1 ))) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  TT && emp 
|--
  “ ((1 <= ((i - 1 ) + 1 )) -> ((k + 1 ) < (2 * n_pre ))) ” 
  &&  “ ((k + 1 ) <= (lower_n + (n_pre - ((i - 1 ) + 1 ) ) )) ” 
  &&  “ (pointf_upper_scan_inv sorted (sublist (0) (lower_n) ((sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))))) (sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ((i - 1 ) + 1 ) (k + 1 ) lower_n ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ) ” 
  &&  “ ((Zlength ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) = (2 * n_pre )) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (lower_n = (Zlength ((sublist (0) (lower_n) ((sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2))))))))))) ”
  &&  emp
).

Definition andrew_build_from_sorted_entail_wit_8_2_split_goal_1 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  ((1 <= ((i - 1 ) + 1 )) -> ((k + 1 ) < (2 * n_pre )))
.

Definition andrew_build_from_sorted_entail_wit_8_2_split_goal_2 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  ((k + 1 ) <= (lower_n + (n_pre - ((i - 1 ) + 1 ) ) ))
.

Definition andrew_build_from_sorted_entail_wit_8_2_split_goal_3 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (pointf_upper_scan_inv sorted (sublist (0) (lower_n) ((sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))))) (sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) ((i - 1 ) + 1 ) (k + 1 ) lower_n )
.

Definition andrew_build_from_sorted_entail_wit_8_2_split_goal_4 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (Forall fp32_isFinite (map (pointf_get_y) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) )
.

Definition andrew_build_from_sorted_entail_wit_8_2_split_goal_5 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (Forall fp32_isFinite (map (pointf_get_x) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) )
.

Definition andrew_build_from_sorted_entail_wit_8_2_split_goal_6 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  ((Zlength ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))) = (2 * n_pre ))
.

Definition andrew_build_from_sorted_entail_wit_8_2_split_goal_7 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))
.

Definition andrew_build_from_sorted_entail_wit_8_2_split_goal_8 := 
forall (n_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all_2: (@list PointF)) (lower_2: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all_2 __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all_2 __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all_2 __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower_2)))) (PreH11 : (lower_2 = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 sorted ) /\ (In pb_2 sorted )) /\ (In pc_2 sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH20 : (pointf_upper_pop_inv sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (lower_n = (Zlength ((sublist (0) (lower_n) ((sublist (0) ((k + 1 )) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)) __default_PointF)))) ((pointf_get_y ((Znth i sorted __default_PointF)))))) ((replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all_2 __default_PointF)))))) (hull_all_2)))))))))))
.

Definition andrew_build_from_sorted_return_wit_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= (i + 1 ))) (PreH5 : ((i + 1 ) <= (n_pre - 1 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k <= (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_scan_inv sorted lower (sublist (0) (k) (hull_all_2)) (i + 1 ) k lower_n )) (PreH20 : (lower_n <= n_pre)) (PreH21 : (k <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH22 : ((1 <= (i + 1 )) -> (k < (2 * n_pre )))) (PreH23 : (((i + 1 ) <= 0) -> (lower_n < k))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all_2 )
|--
  EX (pts_out: (@list PointF))  (hull_all: (@list PointF))  (out: (@list PointF)) ,
  “ (out = (sublist (0) ((k - 1 )) (hull_all))) ” 
  &&  “ ((Zlength (out)) = (k - 1 )) ” 
  &&  “ (is_andrew_hull_float sorted pts_out out ) ”
  &&  (PointFArray.full pts_pre n_pre pts_out )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= (i + 1 ))) (PreH5 : ((i + 1 ) <= (n_pre - 1 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k <= (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_scan_inv sorted lower (sublist (0) (k) (hull_all_2)) (i + 1 ) k lower_n )) (PreH20 : (lower_n <= n_pre)) (PreH21 : (k <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH22 : ((1 <= (i + 1 )) -> (k < (2 * n_pre )))) (PreH23 : (((i + 1 ) <= 0) -> (lower_n < k))) ,
  TT && emp 
|--
  “ (is_andrew_hull_float sorted sorted (sublist (0) ((k - 1 )) (hull_all_2)) ) ” 
  &&  “ ((Zlength ((sublist (0) ((k - 1 )) (hull_all_2)))) = (k - 1 )) ”
  &&  emp
).

Definition andrew_build_from_sorted_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= (i + 1 ))) (PreH5 : ((i + 1 ) <= (n_pre - 1 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k <= (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_scan_inv sorted lower (sublist (0) (k) (hull_all_2)) (i + 1 ) k lower_n )) (PreH20 : (lower_n <= n_pre)) (PreH21 : (k <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH22 : ((1 <= (i + 1 )) -> (k < (2 * n_pre )))) (PreH23 : (((i + 1 ) <= 0) -> (lower_n < k))) ,
  (is_andrew_hull_float sorted sorted (sublist (0) ((k - 1 )) (hull_all_2)) )
.

Definition andrew_build_from_sorted_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (sorted: (@list PointF)) (hull_all_2: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z) (PreH1 : (i < 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= (i + 1 ))) (PreH5 : ((i + 1 ) <= (n_pre - 1 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k <= (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all_2)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all_2)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all_2)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all_2)) )) (PreH19 : (pointf_upper_scan_inv sorted lower (sublist (0) (k) (hull_all_2)) (i + 1 ) k lower_n )) (PreH20 : (lower_n <= n_pre)) (PreH21 : (k <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH22 : ((1 <= (i + 1 )) -> (k < (2 * n_pre )))) (PreH23 : (((i + 1 ) <= 0) -> (lower_n < k))) ,
  ((Zlength ((sublist (0) ((k - 1 )) (hull_all_2)))) = (k - 1 ))
.

Definition andrew_build_from_sorted_partial_solve_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + ((k - 1 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 1 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 1 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 2 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
.

Definition andrew_build_from_sorted_partial_solve_wit_4 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 2 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_5 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + ((k - 1 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 1 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 1 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_6 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 2 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_7 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
.

Definition andrew_build_from_sorted_partial_solve_wit_8 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k >= 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 2 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_9 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k < 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
.

Definition andrew_build_from_sorted_partial_solve_wit_10 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k < 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |->_)
  **  (PointFArray.missing_i hull_pre k 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth k hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_11 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) ) ” 
  &&  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
.

Definition andrew_build_from_sorted_partial_solve_wit_12 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) ) ” 
  &&  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |->_)
  **  (PointFArray.missing_i hull_pre k 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth k hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_13 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k < 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
.

Definition andrew_build_from_sorted_partial_solve_wit_14 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (k < 2)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= i)) (PreH8 : ((Zlength (sorted)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH11 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH12 : (pointf_xy_sorted sorted )) (PreH13 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH16 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
|--
  “ (k < 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |->_)
  **  (PointFArray.missing_i hull_pre k 0 (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
  **  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_15 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) ) ” 
  &&  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
.

Definition andrew_build_from_sorted_partial_solve_wit_16 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (k: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k >= 2)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : ((Zlength (sorted)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : (pointf_xy_sorted sorted )) (PreH14 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH15 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH16 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH17 : (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k )) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
|--
  “ (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) ) ” 
  &&  “ (k >= 2) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_lower_pop_inv sorted before (sublist (0) (k) (hull_all)) i k ) ”
  &&  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |->_)
  **  (PointFArray.missing_i hull_pre k 0 (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
  **  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_17 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + ((k - 1 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 1 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 1 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_18 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 2 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_19 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
.

Definition andrew_build_from_sorted_partial_solve_wit_20 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 2 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_21 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + ((k - 1 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 1 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 1 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_22 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 2 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_23 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
.

Definition andrew_build_from_sorted_partial_solve_wit_24 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k > lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.missing_i hull_pre (k - 2 ) 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + ((k - 2 ) * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_25 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k <= lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
.

Definition andrew_build_from_sorted_partial_solve_wit_26 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (k <= lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |->_)
  **  (PointFArray.missing_i hull_pre k 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth k hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_27 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower)))) (PreH11 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH20 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) ) ” 
  &&  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
.

Definition andrew_build_from_sorted_partial_solve_wit_28 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower)))) (PreH11 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH20 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
|--
  “ (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) ) ” 
  &&  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |->_)
  **  (PointFArray.missing_i hull_pre k 0 (2 * n_pre ) hull_all )
  **  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth k hull_all __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_29 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (k <= lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
.

Definition andrew_build_from_sorted_partial_solve_wit_30 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (k <= lower_n)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= i)) (PreH5 : (i <= (n_pre - 2 ))) (PreH6 : (2 <= lower_n)) (PreH7 : (lower_n <= k)) (PreH8 : (k < (2 * n_pre ))) (PreH9 : (lower_n = (Zlength (lower)))) (PreH10 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH11 : ((Zlength (sorted)) = n_pre)) (PreH12 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH13 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH14 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH15 : (pointf_xy_sorted sorted )) (PreH16 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH17 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH18 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH19 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH20 : (lower_n <= (Zlength (before)))) (PreH21 : (lower_n <= n_pre)) (PreH22 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH23 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH24 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
|--
  “ (k <= lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |->_)
  **  (PointFArray.missing_i hull_pre k 0 (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
  **  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

Definition andrew_build_from_sorted_partial_solve_wit_31 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower)))) (PreH11 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH20 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
  **  (PointFArray.full pts_pre n_pre sorted )
|--
  “ (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) ) ” 
  &&  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |-> (pointf_get_y ((Znth i sorted __default_PointF))))
  **  (PointFArray.missing_i pts_pre i 0 n_pre sorted )
  **  ((&(((pts_pre + (i * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth i sorted __default_PointF))))
  **  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
.

Definition andrew_build_from_sorted_partial_solve_wit_32 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (sorted: (@list PointF)) (before: (@list PointF)) (hull_all: (@list PointF)) (lower: (@list PointF)) (k: Z) (lower_n: Z) (i: Z)  __default_PointF (PreH1 : (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) )) (PreH2 : (k > lower_n)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= (n_pre - 2 ))) (PreH7 : (2 <= lower_n)) (PreH8 : (lower_n <= k)) (PreH9 : (k < (2 * n_pre ))) (PreH10 : (lower_n = (Zlength (lower)))) (PreH11 : (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all)))))) (PreH12 : ((Zlength (sorted)) = n_pre)) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (sorted)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (sorted)) )) (PreH15 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH16 : (pointf_xy_sorted sorted )) (PreH17 : ((Zlength (hull_all)) = (2 * n_pre ))) (PreH18 : (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) )) (PreH19 : (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) )) (PreH20 : (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n )) (PreH21 : (lower_n <= (Zlength (before)))) (PreH22 : (lower_n <= n_pre)) (PreH23 : ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) ))) (PreH24 : ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre )))) (PreH25 : (((i + 1 ) <= 0) -> (lower_n < (Zlength (before))))) ,
  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
|--
  “ (fp32_gt (fp32_sub ((fp32_mul ((fp32_sub ((pointf_get_x ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_y ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))))) ((fp32_mul ((fp32_sub ((pointf_get_y ((Znth (k - 1 ) hull_all __default_PointF)))) ((pointf_get_y ((Znth (k - 2 ) hull_all __default_PointF)))))) ((fp32_sub ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_x ((Znth (k - 2 ) hull_all __default_PointF))))))))) (fp32_of_real (0.0)) ) ” 
  &&  “ (k > lower_n) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (n_pre - 2 )) ” 
  &&  “ (2 <= lower_n) ” 
  &&  “ (lower_n <= k) ” 
  &&  “ (k < (2 * n_pre )) ” 
  &&  “ (lower_n = (Zlength (lower))) ” 
  &&  “ (lower = (sublist (0) (lower_n) ((sublist (0) (k) (hull_all))))) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (sorted)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (sorted)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa sorted ) /\ (In pb sorted )) /\ (In pc sorted )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted sorted ) ” 
  &&  “ ((Zlength (hull_all)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_all)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_all)) ) ” 
  &&  “ (pointf_upper_pop_inv sorted lower before (sublist (0) (k) (hull_all)) i k lower_n ) ” 
  &&  “ (lower_n <= (Zlength (before))) ” 
  &&  “ (lower_n <= n_pre) ” 
  &&  “ ((Zlength (before)) <= (lower_n + (n_pre - (i + 1 ) ) )) ” 
  &&  “ ((1 <= (i + 1 )) -> ((Zlength (before)) < (2 * n_pre ))) ” 
  &&  “ (((i + 1 ) <= 0) -> (lower_n < (Zlength (before)))) ”
  &&  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "y")) # Float  |->_)
  **  (PointFArray.missing_i hull_pre k 0 (2 * n_pre ) (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) )
  **  ((&(((hull_pre + (k * sizeof( "PointF" ))))  # "PointF" ->ₛ "x")) # Float  |-> (pointf_get_x ((Znth k (replace_Znth (k) ((pointf_mk ((pointf_get_x ((Znth i sorted __default_PointF)))) ((pointf_get_y ((Znth k hull_all __default_PointF)))))) (hull_all)) __default_PointF))))
  **  (PointFArray.full pts_pre n_pre sorted )
.

(*----- Function convex_hull_float -----*)

Definition convex_hull_float_safety_wit_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH6 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH7 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full pts_pre n_pre input )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition convex_hull_float_safety_wit_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH6 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH7 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full pts_pre n_pre input )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition convex_hull_float_safety_wit_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH6 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH7 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full pts_pre n_pre input )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition convex_hull_float_return_wit_1 := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out_2: (@list PointF)) (pts_out: (@list PointF)) (hull_all_2: (@list PointF)) (out_3: (@list PointF)) (retval: Z) (PreH1 : (out_3 = (sublist (0) (retval) (hull_all_2)))) (PreH2 : ((Zlength (out_3)) = retval)) (PreH3 : (is_andrew_hull_float out_2 pts_out out_3 )) (PreH4 : (pointf_permutation input out_2 )) (PreH5 : (pointf_same_outside_range input out_2 0 (n_pre - 1 ) )) (PreH6 : (pointf_xy_sorted_range out_2 0 (n_pre - 1 ) )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre pts_out )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all_2 )
|--
  EX (sorted: (@list PointF))  (hull_all: (@list PointF))  (out: (@list PointF)) ,
  “ (out = (sublist (0) (retval) (hull_all))) ” 
  &&  “ ((Zlength (out)) = retval) ” 
  &&  “ (is_andrew_hull_float input sorted out ) ”
  &&  (PointFArray.full pts_pre n_pre sorted )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_all )
) \/
(
forall (n_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out_2: (@list PointF)) (pts_out: (@list PointF)) (hull_all_2: (@list PointF)) (out_3: (@list PointF)) (retval: Z) (PreH1 : (out_3 = (sublist (0) (retval) (hull_all_2)))) (PreH2 : ((Zlength (out_3)) = retval)) (PreH3 : (is_andrew_hull_float out_2 pts_out out_3 )) (PreH4 : (pointf_permutation input out_2 )) (PreH5 : (pointf_same_outside_range input out_2 0 (n_pre - 1 ) )) (PreH6 : (pointf_xy_sorted_range out_2 0 (n_pre - 1 ) )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  TT && emp 
|--
  “ (is_andrew_hull_float input pts_out out_3 ) ”
  &&  emp
).

Definition convex_hull_float_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out_2: (@list PointF)) (pts_out: (@list PointF)) (hull_all_2: (@list PointF)) (out_3: (@list PointF)) (retval: Z) (PreH1 : (out_3 = (sublist (0) (retval) (hull_all_2)))) (PreH2 : ((Zlength (out_3)) = retval)) (PreH3 : (is_andrew_hull_float out_2 pts_out out_3 )) (PreH4 : (pointf_permutation input out_2 )) (PreH5 : (pointf_same_outside_range input out_2 0 (n_pre - 1 ) )) (PreH6 : (pointf_xy_sorted_range out_2 0 (n_pre - 1 ) )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (input)) = n_pre)) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH12 : forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) )))) (PreH13 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH14 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH15 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (is_andrew_hull_float input pts_out out_3 )
.

Definition convex_hull_float_partial_solve_wit_1_pure := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH6 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH7 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full pts_pre n_pre input )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (input)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (input)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH7 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH8 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH9 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full pts_pre n_pre input )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
).

Definition convex_hull_float_partial_solve_wit_1_pure_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (input)) = n_pre)) (PreH6 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH7 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH8 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH9 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH10 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH11 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full pts_pre n_pre input )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
.

Definition convex_hull_float_partial_solve_wit_1_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (input)) = n_pre)) (PreH4 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH5 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH6 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH7 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH8 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH9 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre input )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (input)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (input)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa input ) /\ (In pb input )) /\ (In pc input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (input)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (input)) ) ” 
  &&  “ forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) ))) ” 
  &&  “ ((Zlength (hull_init)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) ) ”
  &&  (PointFArray.full pts_pre n_pre input )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
.

Definition convex_hull_float_partial_solve_wit_1 := convex_hull_float_partial_solve_wit_1_pure -> convex_hull_float_partial_solve_wit_1_aux.

Definition convex_hull_float_partial_solve_wit_2_pure := 
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out: (@list PointF)) (PreH1 : (pointf_permutation input out )) (PreH2 : (pointf_same_outside_range input out 0 (n_pre - 1 ) )) (PreH3 : (pointf_xy_sorted_range out 0 (n_pre - 1 ) )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH10 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH11 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH12 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (hull_init)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) ) ” 
  &&  “ (pointf_xy_sorted out ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ ((Zlength (out)) = n_pre) ”
) \/
(
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out: (@list PointF)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (pointf_permutation input out )) (PreH4 : (pointf_same_outside_range input out 0 (n_pre - 1 ) )) (PreH5 : (pointf_xy_sorted_range out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ ((Zlength (out)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (pointf_xy_sorted out ) ”
).

Definition convex_hull_float_partial_solve_wit_2_pure_split_goal_1 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out: (@list PointF)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (pointf_permutation input out )) (PreH4 : (pointf_same_outside_range input out 0 (n_pre - 1 ) )) (PreH5 : (pointf_xy_sorted_range out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ ((Zlength (out)) = n_pre) ”
.

Definition convex_hull_float_partial_solve_wit_2_pure_split_goal_2 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out: (@list PointF)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (pointf_permutation input out )) (PreH4 : (pointf_same_outside_range input out 0 (n_pre - 1 ) )) (PreH5 : (pointf_xy_sorted_range out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ”
.

Definition convex_hull_float_partial_solve_wit_2_pure_split_goal_3 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out: (@list PointF)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (pointf_permutation input out )) (PreH4 : (pointf_same_outside_range input out 0 (n_pre - 1 ) )) (PreH5 : (pointf_xy_sorted_range out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ”
.

Definition convex_hull_float_partial_solve_wit_2_pure_split_goal_4 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out: (@list PointF)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (pointf_permutation input out )) (PreH4 : (pointf_same_outside_range input out 0 (n_pre - 1 ) )) (PreH5 : (pointf_xy_sorted_range out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ”
.

Definition convex_hull_float_partial_solve_wit_2_pure_split_goal_5 := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out: (@list PointF)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (n_pre >= INT_MIN)) (PreH3 : (pointf_permutation input out )) (PreH4 : (pointf_same_outside_range input out 0 (n_pre - 1 ) )) (PreH5 : (pointf_xy_sorted_range out 0 (n_pre - 1 ) )) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((Zlength (input)) = n_pre)) (PreH9 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH10 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH11 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH12 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH13 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH14 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre out )
  **  ((( &( "pts" ) )) # Ptr  |-> pts_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "hull" ) )) # Ptr  |-> hull_pre)
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (pointf_xy_sorted out ) ”
.

Definition convex_hull_float_partial_solve_wit_2_aux := 
forall (hull_pre: Z) (n_pre: Z) (pts_pre: Z) (hull_init: (@list PointF)) (input: (@list PointF)) (out: (@list PointF)) (PreH1 : (pointf_permutation input out )) (PreH2 : (pointf_same_outside_range input out 0 (n_pre - 1 ) )) (PreH3 : (pointf_xy_sorted_range out 0 (n_pre - 1 ) )) (PreH4 : (2 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (input)) = n_pre)) (PreH7 : (Forall fp32_isFinite (map (pointf_get_x) (input)) )) (PreH8 : (Forall fp32_isFinite (map (pointf_get_y) (input)) )) (PreH9 : forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) )))) (PreH10 : ((Zlength (hull_init)) = (2 * n_pre ))) (PreH11 : (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) )) (PreH12 : (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) )) ,
  (PointFArray.full pts_pre n_pre out )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (hull_init)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) ) ” 
  &&  “ (pointf_xy_sorted out ) ” 
  &&  “ forall (pa: PointF) , forall (pb: PointF) , forall (pc: PointF) , ((((In pa out ) /\ (In pb out )) /\ (In pc out )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb))) ((pointf_get_x (pa))))) ((fp32_sub ((pointf_get_y (pc))) ((pointf_get_y (pa)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb))) ((pointf_get_y (pa))))) ((fp32_sub ((pointf_get_x (pc))) ((pointf_get_x (pa)))))) )) /\ (fp32_isFinite (pointf_cross (pa) (pb) (pc)) ))) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (out)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (out)) ) ” 
  &&  “ ((Zlength (out)) = n_pre) ” 
  &&  “ (pointf_permutation input out ) ” 
  &&  “ (pointf_same_outside_range input out 0 (n_pre - 1 ) ) ” 
  &&  “ (pointf_xy_sorted_range out 0 (n_pre - 1 ) ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (input)) = n_pre) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (input)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (input)) ) ” 
  &&  “ forall (pa_2: PointF) , forall (pb_2: PointF) , forall (pc_2: PointF) , ((((In pa_2 input ) /\ (In pb_2 input )) /\ (In pc_2 input )) -> (((((((fp32_isFinite (fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2)))) ) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2)))) )) /\ (fp32_isFinite (fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_x (pb_2))) ((pointf_get_x (pa_2))))) ((fp32_sub ((pointf_get_y (pc_2))) ((pointf_get_y (pa_2)))))) )) /\ (fp32_isFinite (fp32_mul ((fp32_sub ((pointf_get_y (pb_2))) ((pointf_get_y (pa_2))))) ((fp32_sub ((pointf_get_x (pc_2))) ((pointf_get_x (pa_2)))))) )) /\ (fp32_isFinite (pointf_cross (pa_2) (pb_2) (pc_2)) ))) ” 
  &&  “ ((Zlength (hull_init)) = (2 * n_pre )) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_x) (hull_init)) ) ” 
  &&  “ (Forall fp32_isFinite (map (pointf_get_y) (hull_init)) ) ”
  &&  (PointFArray.full pts_pre n_pre out )
  **  (PointFArray.full hull_pre (2 * n_pre ) hull_init )
.

Definition convex_hull_float_partial_solve_wit_2 := convex_hull_float_partial_solve_wit_2_pure -> convex_hull_float_partial_solve_wit_2_aux.

Module Type VC_Correct.

Include pointf_array_Strategy_Correct.

Axiom proof_of_point_cmp_xy_safety_wit_1 : point_cmp_xy_safety_wit_1.
Axiom proof_of_point_cmp_xy_safety_wit_2 : point_cmp_xy_safety_wit_2.
Axiom proof_of_point_cmp_xy_safety_wit_3 : point_cmp_xy_safety_wit_3.
Axiom proof_of_point_cmp_xy_safety_wit_4 : point_cmp_xy_safety_wit_4.
Axiom proof_of_point_cmp_xy_safety_wit_5 : point_cmp_xy_safety_wit_5.
Axiom proof_of_point_cmp_xy_safety_wit_6 : point_cmp_xy_safety_wit_6.
Axiom proof_of_point_cmp_xy_safety_wit_7 : point_cmp_xy_safety_wit_7.
Axiom proof_of_point_cmp_xy_safety_wit_8 : point_cmp_xy_safety_wit_8.
Axiom proof_of_point_cmp_xy_safety_wit_9 : point_cmp_xy_safety_wit_9.
Axiom proof_of_point_cmp_xy_safety_wit_10 : point_cmp_xy_safety_wit_10.
Axiom proof_of_point_cmp_xy_safety_wit_11 : point_cmp_xy_safety_wit_11.
Axiom proof_of_point_cmp_xy_return_wit_1 : point_cmp_xy_return_wit_1.
Axiom proof_of_point_cmp_xy_return_wit_2 : point_cmp_xy_return_wit_2.
Axiom proof_of_point_cmp_xy_return_wit_3 : point_cmp_xy_return_wit_3.
Axiom proof_of_point_cmp_xy_return_wit_4 : point_cmp_xy_return_wit_4.
Axiom proof_of_point_cmp_xy_return_wit_5 : point_cmp_xy_return_wit_5.
Axiom proof_of_point_cross_safety_wit_1 : point_cross_safety_wit_1.
Axiom proof_of_point_cross_safety_wit_2 : point_cross_safety_wit_2.
Axiom proof_of_point_cross_safety_wit_3 : point_cross_safety_wit_3.
Axiom proof_of_point_cross_safety_wit_4 : point_cross_safety_wit_4.
Axiom proof_of_point_cross_safety_wit_5 : point_cross_safety_wit_5.
Axiom proof_of_point_cross_safety_wit_6 : point_cross_safety_wit_6.
Axiom proof_of_point_cross_safety_wit_7 : point_cross_safety_wit_7.
Axiom proof_of_point_cross_return_wit_1 : point_cross_return_wit_1.
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
Axiom proof_of_partition_xy_points_partial_solve_wit_5_pure : partition_xy_points_partial_solve_wit_5_pure.
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
Axiom proof_of_andrew_build_from_sorted_safety_wit_36 : andrew_build_from_sorted_safety_wit_36.
Axiom proof_of_andrew_build_from_sorted_safety_wit_37 : andrew_build_from_sorted_safety_wit_37.
Axiom proof_of_andrew_build_from_sorted_safety_wit_38 : andrew_build_from_sorted_safety_wit_38.
Axiom proof_of_andrew_build_from_sorted_safety_wit_39 : andrew_build_from_sorted_safety_wit_39.
Axiom proof_of_andrew_build_from_sorted_safety_wit_40 : andrew_build_from_sorted_safety_wit_40.
Axiom proof_of_andrew_build_from_sorted_safety_wit_41 : andrew_build_from_sorted_safety_wit_41.
Axiom proof_of_andrew_build_from_sorted_safety_wit_42 : andrew_build_from_sorted_safety_wit_42.
Axiom proof_of_andrew_build_from_sorted_safety_wit_43 : andrew_build_from_sorted_safety_wit_43.
Axiom proof_of_andrew_build_from_sorted_safety_wit_44 : andrew_build_from_sorted_safety_wit_44.
Axiom proof_of_andrew_build_from_sorted_safety_wit_45 : andrew_build_from_sorted_safety_wit_45.
Axiom proof_of_andrew_build_from_sorted_safety_wit_46 : andrew_build_from_sorted_safety_wit_46.
Axiom proof_of_andrew_build_from_sorted_safety_wit_47 : andrew_build_from_sorted_safety_wit_47.
Axiom proof_of_andrew_build_from_sorted_safety_wit_48 : andrew_build_from_sorted_safety_wit_48.
Axiom proof_of_andrew_build_from_sorted_safety_wit_49 : andrew_build_from_sorted_safety_wit_49.
Axiom proof_of_andrew_build_from_sorted_safety_wit_50 : andrew_build_from_sorted_safety_wit_50.
Axiom proof_of_andrew_build_from_sorted_safety_wit_51 : andrew_build_from_sorted_safety_wit_51.
Axiom proof_of_andrew_build_from_sorted_safety_wit_52 : andrew_build_from_sorted_safety_wit_52.
Axiom proof_of_andrew_build_from_sorted_safety_wit_53 : andrew_build_from_sorted_safety_wit_53.
Axiom proof_of_andrew_build_from_sorted_safety_wit_54 : andrew_build_from_sorted_safety_wit_54.
Axiom proof_of_andrew_build_from_sorted_safety_wit_55 : andrew_build_from_sorted_safety_wit_55.
Axiom proof_of_andrew_build_from_sorted_safety_wit_56 : andrew_build_from_sorted_safety_wit_56.
Axiom proof_of_andrew_build_from_sorted_safety_wit_57 : andrew_build_from_sorted_safety_wit_57.
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
Axiom proof_of_andrew_build_from_sorted_return_wit_1 : andrew_build_from_sorted_return_wit_1.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_1 : andrew_build_from_sorted_partial_solve_wit_1.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_2 : andrew_build_from_sorted_partial_solve_wit_2.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_3 : andrew_build_from_sorted_partial_solve_wit_3.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_4 : andrew_build_from_sorted_partial_solve_wit_4.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_5 : andrew_build_from_sorted_partial_solve_wit_5.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_6 : andrew_build_from_sorted_partial_solve_wit_6.
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
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_20 : andrew_build_from_sorted_partial_solve_wit_20.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_21 : andrew_build_from_sorted_partial_solve_wit_21.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_22 : andrew_build_from_sorted_partial_solve_wit_22.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_23 : andrew_build_from_sorted_partial_solve_wit_23.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_24 : andrew_build_from_sorted_partial_solve_wit_24.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_25 : andrew_build_from_sorted_partial_solve_wit_25.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_26 : andrew_build_from_sorted_partial_solve_wit_26.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_27 : andrew_build_from_sorted_partial_solve_wit_27.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_28 : andrew_build_from_sorted_partial_solve_wit_28.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_29 : andrew_build_from_sorted_partial_solve_wit_29.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_30 : andrew_build_from_sorted_partial_solve_wit_30.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_31 : andrew_build_from_sorted_partial_solve_wit_31.
Axiom proof_of_andrew_build_from_sorted_partial_solve_wit_32 : andrew_build_from_sorted_partial_solve_wit_32.
Axiom proof_of_convex_hull_float_safety_wit_1 : convex_hull_float_safety_wit_1.
Axiom proof_of_convex_hull_float_safety_wit_2 : convex_hull_float_safety_wit_2.
Axiom proof_of_convex_hull_float_safety_wit_3 : convex_hull_float_safety_wit_3.
Axiom proof_of_convex_hull_float_return_wit_1 : convex_hull_float_return_wit_1.
Axiom proof_of_convex_hull_float_partial_solve_wit_1_pure : convex_hull_float_partial_solve_wit_1_pure.
Axiom proof_of_convex_hull_float_partial_solve_wit_1 : convex_hull_float_partial_solve_wit_1.
Axiom proof_of_convex_hull_float_partial_solve_wit_2_pure : convex_hull_float_partial_solve_wit_2_pure.
Axiom proof_of_convex_hull_float_partial_solve_wit_2 : convex_hull_float_partial_solve_wit_2.

End VC_Correct.
