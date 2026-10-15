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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P071_2044H_hard_demon_problem_lib.
Local Open Scope sac.

(*----- Function rect -----*)

Definition rect_safety_wit_1 := 
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) )) ”
) \/
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) )) ”
).

Definition rect_safety_wit_1_split_goal_1 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) <= INT64_MAX) ”
.

Definition rect_safety_wit_1_split_goal_2 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((INT64_MIN) <= ((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) )) ”
.

Definition rect_safety_wit_2 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 )) ”
.

Definition rect_safety_wit_3 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((x1_pre - 1 ) * stride_pre ) + y1_pre )) ”
.

Definition rect_safety_wit_4 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((x1_pre - 1 ) * stride_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x1_pre - 1 ) * stride_pre )) ”
.

Definition rect_safety_wit_5 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((x1_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x1_pre - 1 )) ”
.

Definition rect_safety_wit_6 := 
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) )) ”
) \/
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) )) ”
).

Definition rect_safety_wit_6_split_goal_1 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) <= INT64_MAX) ”
.

Definition rect_safety_wit_6_split_goal_2 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((INT64_MIN) <= (((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) )) ”
.

Definition rect_safety_wit_7 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((x2_pre * stride_pre ) + y1_pre ) - 1 )) ”
.

Definition rect_safety_wit_8 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((x2_pre * stride_pre ) + y1_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x2_pre * stride_pre ) + y1_pre )) ”
.

Definition rect_safety_wit_9 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((x2_pre * stride_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x2_pre * stride_pre )) ”
.

Definition rect_safety_wit_10 := 
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) )) ”
) \/
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) )) ”
).

Definition rect_safety_wit_10_split_goal_1 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) <= INT64_MAX) ”
.

Definition rect_safety_wit_10_split_goal_2 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((INT64_MIN) <= ((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) )) ”
.

Definition rect_safety_wit_11 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((x1_pre - 1 ) * stride_pre ) + y2_pre )) ”
.

Definition rect_safety_wit_12 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (((x1_pre - 1 ) * stride_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x1_pre - 1 ) * stride_pre )) ”
.

Definition rect_safety_wit_13 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ ((x1_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x1_pre - 1 )) ”
.

Definition rect_safety_wit_14 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
|--
  “ (((x2_pre * stride_pre ) + y2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((x2_pre * stride_pre ) + y2_pre )) ”
.

Definition rect_safety_wit_15 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
|--
  “ ((x2_pre * stride_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (x2_pre * stride_pre )) ”
.

Definition rect_safety_wit_16 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rect_safety_wit_17 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rect_safety_wit_18 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rect_safety_wit_19 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rect_entail_wit_1 := 
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (2 <= stride_pre)) (PreH2 : (stride_pre <= 2001)) (PreH3 : (1 <= x1_pre)) (PreH4 : (x1_pre <= x2_pre)) (PreH5 : (x2_pre < stride_pre)) (PreH6 : (1 <= y1_pre)) (PreH7 : (y1_pre <= y2_pre)) (PreH8 : (y2_pre < stride_pre)) (PreH9 : (0 <= bound_rect_spec)) (PreH10 : (bound_rect_spec <= 4002000000000000)) (PreH11 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH12 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH13 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
|--
  “ (0 <= ((x2_pre * stride_pre ) + y2_pre )) ” 
  &&  “ (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre )) ” 
  &&  “ ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (2 <= stride_pre) ” 
  &&  “ (stride_pre <= 2001) ” 
  &&  “ (1 <= x1_pre) ” 
  &&  “ (x1_pre <= x2_pre) ” 
  &&  “ (x2_pre < stride_pre) ” 
  &&  “ (1 <= y1_pre) ” 
  &&  “ (y1_pre <= y2_pre) ” 
  &&  “ (y2_pre < stride_pre) ” 
  &&  “ (0 <= bound_rect_spec) ” 
  &&  “ (bound_rect_spec <= 4002000000000000) ” 
  &&  “ ((Zlength (values_rect_spec)) = (stride_pre * stride_pre )) ” 
  &&  “ (RectanglesBounded values_rect_spec stride_pre bound_rect_spec ) ” 
  &&  “ (RectIntermediatesSafe values_rect_spec stride_pre ) ”
  &&  ((( &( "x2" ) )) # Int  |-> x2_pre)
  **  ((( &( "stride" ) )) # Int  |-> stride_pre)
  **  ((( &( "y2" ) )) # Int  |-> y2_pre)
  **  ((( &( "x1" ) )) # Int  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int  |-> y1_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
) \/
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (y2_pre <= INT_MAX)) (PreH2 : (x2_pre <= INT_MAX)) (PreH3 : (y1_pre <= INT_MAX)) (PreH4 : (x1_pre <= INT_MAX)) (PreH5 : (stride_pre <= INT_MAX)) (PreH6 : (y2_pre >= INT_MIN)) (PreH7 : (x2_pre >= INT_MIN)) (PreH8 : (y1_pre >= INT_MIN)) (PreH9 : (x1_pre >= INT_MIN)) (PreH10 : (stride_pre >= INT_MIN)) (PreH11 : (2 <= stride_pre)) (PreH12 : (stride_pre <= 2001)) (PreH13 : (1 <= x1_pre)) (PreH14 : (x1_pre <= x2_pre)) (PreH15 : (x2_pre < stride_pre)) (PreH16 : (1 <= y1_pre)) (PreH17 : (y1_pre <= y2_pre)) (PreH18 : (y2_pre < stride_pre)) (PreH19 : (0 <= bound_rect_spec)) (PreH20 : (bound_rect_spec <= 4002000000000000)) (PreH21 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH22 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH23 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  TT && emp 
|--
  “ (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ”
  &&  emp
).

Definition rect_entail_wit_1_split_goal_1 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (y2_pre <= INT_MAX)) (PreH2 : (x2_pre <= INT_MAX)) (PreH3 : (y1_pre <= INT_MAX)) (PreH4 : (x1_pre <= INT_MAX)) (PreH5 : (stride_pre <= INT_MAX)) (PreH6 : (y2_pre >= INT_MIN)) (PreH7 : (x2_pre >= INT_MIN)) (PreH8 : (y1_pre >= INT_MIN)) (PreH9 : (x1_pre >= INT_MIN)) (PreH10 : (stride_pre >= INT_MIN)) (PreH11 : (2 <= stride_pre)) (PreH12 : (stride_pre <= 2001)) (PreH13 : (1 <= x1_pre)) (PreH14 : (x1_pre <= x2_pre)) (PreH15 : (x2_pre < stride_pre)) (PreH16 : (1 <= y1_pre)) (PreH17 : (y1_pre <= y2_pre)) (PreH18 : (y2_pre < stride_pre)) (PreH19 : (0 <= bound_rect_spec)) (PreH20 : (bound_rect_spec <= 4002000000000000)) (PreH21 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH22 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH23 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))
.

Definition rect_entail_wit_1_split_goal_2 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (y2_pre <= INT_MAX)) (PreH2 : (x2_pre <= INT_MAX)) (PreH3 : (y1_pre <= INT_MAX)) (PreH4 : (x1_pre <= INT_MAX)) (PreH5 : (stride_pre <= INT_MAX)) (PreH6 : (y2_pre >= INT_MIN)) (PreH7 : (x2_pre >= INT_MIN)) (PreH8 : (y1_pre >= INT_MIN)) (PreH9 : (x1_pre >= INT_MIN)) (PreH10 : (stride_pre >= INT_MIN)) (PreH11 : (2 <= stride_pre)) (PreH12 : (stride_pre <= 2001)) (PreH13 : (1 <= x1_pre)) (PreH14 : (x1_pre <= x2_pre)) (PreH15 : (x2_pre < stride_pre)) (PreH16 : (1 <= y1_pre)) (PreH17 : (y1_pre <= y2_pre)) (PreH18 : (y2_pre < stride_pre)) (PreH19 : (0 <= bound_rect_spec)) (PreH20 : (bound_rect_spec <= 4002000000000000)) (PreH21 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH22 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH23 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))
.

Definition rect_entail_wit_1_split_goal_3 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (y2_pre <= INT_MAX)) (PreH2 : (x2_pre <= INT_MAX)) (PreH3 : (y1_pre <= INT_MAX)) (PreH4 : (x1_pre <= INT_MAX)) (PreH5 : (stride_pre <= INT_MAX)) (PreH6 : (y2_pre >= INT_MIN)) (PreH7 : (x2_pre >= INT_MIN)) (PreH8 : (y1_pre >= INT_MIN)) (PreH9 : (x1_pre >= INT_MIN)) (PreH10 : (stride_pre >= INT_MIN)) (PreH11 : (2 <= stride_pre)) (PreH12 : (stride_pre <= 2001)) (PreH13 : (1 <= x1_pre)) (PreH14 : (x1_pre <= x2_pre)) (PreH15 : (x2_pre < stride_pre)) (PreH16 : (1 <= y1_pre)) (PreH17 : (y1_pre <= y2_pre)) (PreH18 : (y2_pre < stride_pre)) (PreH19 : (0 <= bound_rect_spec)) (PreH20 : (bound_rect_spec <= 4002000000000000)) (PreH21 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH22 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH23 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))
.

Definition rect_entail_wit_1_split_goal_4 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (y2_pre <= INT_MAX)) (PreH2 : (x2_pre <= INT_MAX)) (PreH3 : (y1_pre <= INT_MAX)) (PreH4 : (x1_pre <= INT_MAX)) (PreH5 : (stride_pre <= INT_MAX)) (PreH6 : (y2_pre >= INT_MIN)) (PreH7 : (x2_pre >= INT_MIN)) (PreH8 : (y1_pre >= INT_MIN)) (PreH9 : (x1_pre >= INT_MIN)) (PreH10 : (stride_pre >= INT_MIN)) (PreH11 : (2 <= stride_pre)) (PreH12 : (stride_pre <= 2001)) (PreH13 : (1 <= x1_pre)) (PreH14 : (x1_pre <= x2_pre)) (PreH15 : (x2_pre < stride_pre)) (PreH16 : (1 <= y1_pre)) (PreH17 : (y1_pre <= y2_pre)) (PreH18 : (y2_pre < stride_pre)) (PreH19 : (0 <= bound_rect_spec)) (PreH20 : (bound_rect_spec <= 4002000000000000)) (PreH21 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH22 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH23 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))
.

Definition rect_return_wit_1 := 
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
|--
  “ (((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) = (RectLookup (values_rect_spec) (stride_pre) (x1_pre) (y1_pre) (x2_pre) (y2_pre))) ” 
  &&  “ (0 <= ((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) )) ” 
  &&  “ (((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) <= bound_rect_spec) ”
  &&  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
) \/
(
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  TT && emp 
|--
  “ (((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) <= bound_rect_spec) ” 
  &&  “ (0 <= ((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) )) ” 
  &&  “ (((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) = (RectLookup (values_rect_spec) (stride_pre) (x1_pre) (y1_pre) (x2_pre) (y2_pre))) ”
  &&  emp
).

Definition rect_return_wit_1_split_goal_1 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) <= bound_rect_spec)
.

Definition rect_return_wit_1_split_goal_2 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (0 <= ((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ))
.

Definition rect_return_wit_1_split_goal_3 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (((((Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0) - (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0) ) - (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) + (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0) ) = (RectLookup (values_rect_spec) (stride_pre) (x1_pre) (y1_pre) (x2_pre) (y2_pre)))
.

Definition rect_partial_solve_wit_1 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
|--
  “ (0 <= ((x2_pre * stride_pre ) + y2_pre )) ” 
  &&  “ (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre )) ” 
  &&  “ ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (2 <= stride_pre) ” 
  &&  “ (stride_pre <= 2001) ” 
  &&  “ (1 <= x1_pre) ” 
  &&  “ (x1_pre <= x2_pre) ” 
  &&  “ (x2_pre < stride_pre) ” 
  &&  “ (1 <= y1_pre) ” 
  &&  “ (y1_pre <= y2_pre) ” 
  &&  “ (y2_pre < stride_pre) ” 
  &&  “ (0 <= bound_rect_spec) ” 
  &&  “ (bound_rect_spec <= 4002000000000000) ” 
  &&  “ ((Zlength (values_rect_spec)) = (stride_pre * stride_pre )) ” 
  &&  “ (RectanglesBounded values_rect_spec stride_pre bound_rect_spec ) ” 
  &&  “ (RectIntermediatesSafe values_rect_spec stride_pre ) ”
  &&  (((p_pre + (((x2_pre * stride_pre ) + y2_pre ) * sizeof(INT64)))) # Int64  |-> (Znth ((x2_pre * stride_pre ) + y2_pre ) values_rect_spec 0))
  **  (Int64Array.missing_i p_pre ((x2_pre * stride_pre ) + y2_pre ) 0 (stride_pre * stride_pre ) values_rect_spec )
.

Definition rect_partial_solve_wit_2 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
|--
  “ (0 <= ((x2_pre * stride_pre ) + y2_pre )) ” 
  &&  “ (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre )) ” 
  &&  “ ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (2 <= stride_pre) ” 
  &&  “ (stride_pre <= 2001) ” 
  &&  “ (1 <= x1_pre) ” 
  &&  “ (x1_pre <= x2_pre) ” 
  &&  “ (x2_pre < stride_pre) ” 
  &&  “ (1 <= y1_pre) ” 
  &&  “ (y1_pre <= y2_pre) ” 
  &&  “ (y2_pre < stride_pre) ” 
  &&  “ (0 <= bound_rect_spec) ” 
  &&  “ (bound_rect_spec <= 4002000000000000) ” 
  &&  “ ((Zlength (values_rect_spec)) = (stride_pre * stride_pre )) ” 
  &&  “ (RectanglesBounded values_rect_spec stride_pre bound_rect_spec ) ” 
  &&  “ (RectIntermediatesSafe values_rect_spec stride_pre ) ”
  &&  (((p_pre + ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) * sizeof(INT64)))) # Int64  |-> (Znth (((x1_pre - 1 ) * stride_pre ) + y2_pre ) values_rect_spec 0))
  **  (Int64Array.missing_i p_pre (((x1_pre - 1 ) * stride_pre ) + y2_pre ) 0 (stride_pre * stride_pre ) values_rect_spec )
.

Definition rect_partial_solve_wit_3 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
|--
  “ (0 <= ((x2_pre * stride_pre ) + y2_pre )) ” 
  &&  “ (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre )) ” 
  &&  “ ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (2 <= stride_pre) ” 
  &&  “ (stride_pre <= 2001) ” 
  &&  “ (1 <= x1_pre) ” 
  &&  “ (x1_pre <= x2_pre) ” 
  &&  “ (x2_pre < stride_pre) ” 
  &&  “ (1 <= y1_pre) ” 
  &&  “ (y1_pre <= y2_pre) ” 
  &&  “ (y2_pre < stride_pre) ” 
  &&  “ (0 <= bound_rect_spec) ” 
  &&  “ (bound_rect_spec <= 4002000000000000) ” 
  &&  “ ((Zlength (values_rect_spec)) = (stride_pre * stride_pre )) ” 
  &&  “ (RectanglesBounded values_rect_spec stride_pre bound_rect_spec ) ” 
  &&  “ (RectIntermediatesSafe values_rect_spec stride_pre ) ”
  &&  (((p_pre + ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (((x2_pre * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0))
  **  (Int64Array.missing_i p_pre (((x2_pre * stride_pre ) + y1_pre ) - 1 ) 0 (stride_pre * stride_pre ) values_rect_spec )
.

Definition rect_partial_solve_wit_4 := 
forall (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (stride_pre: Z) (p_pre: Z) (bound_rect_spec: Z) (values_rect_spec: (@list Z)) (PreH1 : (0 <= ((x2_pre * stride_pre ) + y2_pre ))) (PreH2 : (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH3 : (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre ))) (PreH4 : ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre ))) (PreH5 : (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 ))) (PreH6 : ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH7 : (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ))) (PreH8 : (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre ))) (PreH9 : (2 <= stride_pre)) (PreH10 : (stride_pre <= 2001)) (PreH11 : (1 <= x1_pre)) (PreH12 : (x1_pre <= x2_pre)) (PreH13 : (x2_pre < stride_pre)) (PreH14 : (1 <= y1_pre)) (PreH15 : (y1_pre <= y2_pre)) (PreH16 : (y2_pre < stride_pre)) (PreH17 : (0 <= bound_rect_spec)) (PreH18 : (bound_rect_spec <= 4002000000000000)) (PreH19 : ((Zlength (values_rect_spec)) = (stride_pre * stride_pre ))) (PreH20 : (RectanglesBounded values_rect_spec stride_pre bound_rect_spec )) (PreH21 : (RectIntermediatesSafe values_rect_spec stride_pre )) ,
  (Int64Array.full p_pre (stride_pre * stride_pre ) values_rect_spec )
|--
  “ (0 <= ((x2_pre * stride_pre ) + y2_pre )) ” 
  &&  “ (((x2_pre * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x1_pre - 1 ) * stride_pre ) + y2_pre )) ” 
  &&  “ ((((x1_pre - 1 ) * stride_pre ) + y2_pre ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= (((x2_pre * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ ((((x2_pre * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (0 <= ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 )) ” 
  &&  “ (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) < (stride_pre * stride_pre )) ” 
  &&  “ (2 <= stride_pre) ” 
  &&  “ (stride_pre <= 2001) ” 
  &&  “ (1 <= x1_pre) ” 
  &&  “ (x1_pre <= x2_pre) ” 
  &&  “ (x2_pre < stride_pre) ” 
  &&  “ (1 <= y1_pre) ” 
  &&  “ (y1_pre <= y2_pre) ” 
  &&  “ (y2_pre < stride_pre) ” 
  &&  “ (0 <= bound_rect_spec) ” 
  &&  “ (bound_rect_spec <= 4002000000000000) ” 
  &&  “ ((Zlength (values_rect_spec)) = (stride_pre * stride_pre )) ” 
  &&  “ (RectanglesBounded values_rect_spec stride_pre bound_rect_spec ) ” 
  &&  “ (RectIntermediatesSafe values_rect_spec stride_pre ) ”
  &&  (((p_pre + (((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) values_rect_spec 0))
  **  (Int64Array.missing_i p_pre ((((x1_pre - 1 ) * stride_pre ) + y1_pre ) - 1 ) 0 (stride_pre * stride_pre ) values_rect_spec )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z))  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000)) (PreH3 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH4 : (MatrixValuesBounded matrix_data n_pre )) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 1000000)) (PreH7 : (QueriesBounded queries_data n_pre )) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH9 : (q_pre = (Zlength (queries_data)))) (PreH10 : (RawQueriesEncode queries_data raw_queries )) ,
  ((( &( "S" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition solver_safety_wit_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z))  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000)) (PreH3 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH4 : (MatrixValuesBounded matrix_data n_pre )) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 1000000)) (PreH7 : (QueriesBounded queries_data n_pre )) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH9 : (q_pre = (Zlength (queries_data)))) (PreH10 : (RawQueriesEncode queries_data raw_queries )) ,
  ((( &( "S" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH7 : (MatrixValuesBounded matrix_data n_pre )) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 1000000)) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : (RawQueriesEncode queries_data raw_queries )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (Int64Array.full retval_3 ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  ((( &( "col" ) )) # Ptr  |-> retval_3)
  **  (Int64Array.full retval_2 ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  ((( &( "row" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.full retval ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  ((( &( "sum" ) )) # Ptr  |-> retval)
  **  ((( &( "cells" ) )) # UInt  |-> ((n_pre + 1 ) * (n_pre + 1 ) ))
  **  ((( &( "S" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_4 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i <= n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (PrefixTables matrix_data sum_l row_l col_l n_pre S (i * S ) )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH2 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (S >= INT_MIN)) (PreH8 : (q_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH2 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (S >= INT_MIN)) (PreH8 : (q_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((i - 1 ) * n_pre ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - 1 ) * n_pre ) + j )) ”
.

Definition solver_safety_wit_7 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH2 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (S >= INT_MIN)) (PreH8 : (q_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((i - 1 ) * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - 1 ) * n_pre )) ”
.

Definition solver_safety_wit_8 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH2 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (S >= INT_MIN)) (PreH8 : (q_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH2 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (S >= INT_MIN)) (PreH8 : (q_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH2 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (S >= INT_MIN)) (PreH8 : (q_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((( &( "x" ) )) # Int64  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_11 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) ”
).

Definition solver_safety_wit_11_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_11_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((INT64_MIN) <= ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) ”
.

Definition solver_safety_wit_12 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) )) ”
).

Definition solver_safety_wit_12_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_12_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((INT64_MIN) <= (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) )) ”
.

Definition solver_safety_wit_13 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) )) ”
).

Definition solver_safety_wit_13_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_13_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((INT64_MIN) <= ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) )) ”
.

Definition solver_safety_wit_14 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_15 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_16 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) ”
).

Definition solver_safety_wit_16_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_16_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((INT64_MIN) <= (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) ”
.

Definition solver_safety_wit_17 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) )) ”
).

Definition solver_safety_wit_17_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_17_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((INT64_MIN) <= ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) )) ”
.

Definition solver_safety_wit_18 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) )) ”
).

Definition solver_safety_wit_18_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_18_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((INT64_MIN) <= (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) )) ”
.

Definition solver_safety_wit_19 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i )) ”
).

Definition solver_safety_wit_19_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) <= INT64_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((INT64_MIN) <= ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i )) ”
.

Definition solver_safety_wit_20 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_21 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_22 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) col_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) col_l 0) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) col_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) col_l 0) )) ”
).

Definition solver_safety_wit_22_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) col_l 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_22_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((INT64_MIN) <= (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) col_l 0) )) ”
.

Definition solver_safety_wit_23 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) )) ”
).

Definition solver_safety_wit_23_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_23_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((INT64_MIN) <= ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) )) ”
.

Definition solver_safety_wit_24 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) )) ”
).

Definition solver_safety_wit_24_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_24_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((INT64_MIN) <= (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) )) ”
.

Definition solver_safety_wit_25 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j )) ”
).

Definition solver_safety_wit_25_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) <= INT64_MAX) ”
.

Definition solver_safety_wit_25_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((INT64_MIN) <= ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j )) ”
.

Definition solver_safety_wit_26 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_27 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_28 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (j > n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= (n_pre + 1 ))) (PreH17 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_29 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) col_l 0) )) (col_l)) )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_30 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (S: Z) (cells: Z) (sum: Z) (row: Z) (col: Z) (PreH1 : (S = (n_pre + 1 ))) (PreH2 : (cells = (S * S ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 1000000)) (PreH7 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH8 : ((Zlength (queries_data)) = q_pre)) (PreH9 : (MatrixValuesBounded matrix_data n_pre )) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : (RawQueriesEncode queries_data raw_queries )) (PreH12 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "y2" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "x2" ) )) # Int  |-> (Znth ((4 * i ) + 2 ) raw_queries 0))
  **  ((( &( "y1" ) )) # Int  |-> (Znth ((4 * i ) + 1 ) raw_queries 0))
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((4 * i ) + 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((4 * i ) + 3 )) ”
.

Definition solver_safety_wit_32 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "y2" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "x2" ) )) # Int  |-> (Znth ((4 * i ) + 2 ) raw_queries 0))
  **  ((( &( "y1" ) )) # Int  |-> (Znth ((4 * i ) + 1 ) raw_queries 0))
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((4 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (4 * i )) ”
.

Definition solver_safety_wit_33 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "y2" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "x2" ) )) # Int  |-> (Znth ((4 * i ) + 2 ) raw_queries 0))
  **  ((( &( "y1" ) )) # Int  |-> (Znth ((4 * i ) + 1 ) raw_queries 0))
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_34 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "y2" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "x2" ) )) # Int  |-> (Znth ((4 * i ) + 2 ) raw_queries 0))
  **  ((( &( "y1" ) )) # Int  |-> (Znth ((4 * i ) + 1 ) raw_queries 0))
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition solver_safety_wit_35 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "x2" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "y1" ) )) # Int  |-> (Znth ((4 * i ) + 1 ) raw_queries 0))
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((4 * i ) + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((4 * i ) + 2 )) ”
.

Definition solver_safety_wit_36 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "x2" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "y1" ) )) # Int  |-> (Znth ((4 * i ) + 1 ) raw_queries 0))
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((4 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (4 * i )) ”
.

Definition solver_safety_wit_37 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "x2" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "y1" ) )) # Int  |-> (Znth ((4 * i ) + 1 ) raw_queries 0))
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_38 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "x2" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "y1" ) )) # Int  |-> (Znth ((4 * i ) + 1 ) raw_queries 0))
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_39 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "y1" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (((4 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((4 * i ) + 1 )) ”
.

Definition solver_safety_wit_40 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "y1" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((4 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (4 * i )) ”
.

Definition solver_safety_wit_41 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "y1" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_42 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "y1" ) )) # Int  |->_)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "x1" ) )) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_43 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "x1" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((4 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (4 * i )) ”
.

Definition solver_safety_wit_44 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "x1" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition solver_safety_wit_45 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |->_)
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((y2 - y1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((y2 - y1 ) + 1 )) ”
.

Definition solver_safety_wit_46 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |->_)
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((y2 - y1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y2 - y1 )) ”
.

Definition solver_safety_wit_47 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |->_)
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_48 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) )) ”
).

Definition solver_safety_wit_48_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_48_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((INT64_MIN) <= (((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) )) ”
.

Definition solver_safety_wit_49 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((y1 - 1 ) * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((y1 - 1 ) * retval )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((y1 - 1 ) * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((y1 - 1 ) * retval )) ”
).

Definition solver_safety_wit_49_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((y1 - 1 ) * retval ) <= INT64_MAX) ”
.

Definition solver_safety_wit_49_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((INT64_MIN) <= ((y1 - 1 ) * retval )) ”
.

Definition solver_safety_wit_50 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((y1 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (y1 - 1 )) ”
.

Definition solver_safety_wit_51 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 )) ”
).

Definition solver_safety_wit_51_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) <= INT64_MAX) ”
.

Definition solver_safety_wit_51_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((INT64_MIN) <= ((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 )) ”
.

Definition solver_safety_wit_52 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) )) ”
).

Definition solver_safety_wit_52_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_52_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((INT64_MIN) <= (((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) )) ”
.

Definition solver_safety_wit_53 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((retval_2 - (x1 * retval ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval_2 - (x1 * retval ) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((retval_2 - (x1 * retval ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (retval_2 - (x1 * retval ) )) ”
).

Definition solver_safety_wit_53_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((retval_2 - (x1 * retval ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_53_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((INT64_MIN) <= (retval_2 - (x1 * retval ) )) ”
.

Definition solver_safety_wit_54 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((x1 * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (x1 * retval )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((x1 * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (x1 * retval )) ”
).

Definition solver_safety_wit_54_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((x1 * retval ) <= INT64_MAX) ”
.

Definition solver_safety_wit_54_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((INT64_MIN) <= (x1 * retval )) ”
.

Definition solver_safety_wit_55 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "w" ) )) # Int64  |-> ((y2 - y1 ) + 1 ))
  **  (Int64Array.full col (S * S ) col_l )
  **  ((( &( "cs" ) )) # Int64  |-> retval_3)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_56 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (Int64Array.seg out_pre 0 (i + 1 ) (app (result) ((cons ((((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) q_pre )
  **  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH7 : (MatrixValuesBounded matrix_data n_pre )) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 1000000)) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : (RawQueriesEncode queries_data raw_queries )) ,
  (Int64Array.full retval_3 ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  (Int64Array.full retval_2 ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  (Int64Array.full retval ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  EX (sum_l: (@list Z))  (row_l: (@list Z))  (col_l: (@list Z)) ,
  “ ((n_pre + 1 ) = (n_pre + 1 )) ” 
  &&  “ (((n_pre + 1 ) * (n_pre + 1 ) ) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre (n_pre + 1 ) (1 * (n_pre + 1 ) ) ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full retval ((n_pre + 1 ) * (n_pre + 1 ) ) sum_l )
  **  (Int64Array.full retval_2 ((n_pre + 1 ) * (n_pre + 1 ) ) row_l )
  **  (Int64Array.full retval_3 ((n_pre + 1 ) * (n_pre + 1 ) ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH7 : (MatrixValuesBounded matrix_data n_pre )) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 1000000)) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : (RawQueriesEncode queries_data raw_queries )) ,
  TT && emp 
|--
  “ (PrefixTables matrix_data (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) n_pre (n_pre + 1 ) (1 * (n_pre + 1 ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH7 : (MatrixValuesBounded matrix_data n_pre )) (PreH8 : (1 <= (Zlength (queries_data)))) (PreH9 : ((Zlength (queries_data)) <= 1000000)) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH12 : (q_pre = (Zlength (queries_data)))) (PreH13 : (RawQueriesEncode queries_data raw_queries )) ,
  (PrefixTables matrix_data (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) n_pre (n_pre + 1 ) (1 * (n_pre + 1 ) ) )
.

Definition solver_entail_wit_2 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i <= n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S (i * S ) )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l_2 )
  **  (Int64Array.full row (S * S ) row_l_2 )
  **  (Int64Array.full col (S * S ) col_l_2 )
|--
  EX (sum_l: (@list Z))  (row_l: (@list Z))  (col_l: (@list Z)) ,
  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + 1 ) ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i <= n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S (i * S ) )) ,
  TT && emp 
|--
  “ (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre (n_pre + 1 ) ((i * (n_pre + 1 ) ) + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i <= n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S (i * S ) )) ,
  (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre (n_pre + 1 ) ((i * (n_pre + 1 ) ) + 1 ) )
.

Definition solver_entail_wit_3 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (j <= n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= (n_pre + 1 ))) (PreH17 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (cells <= UINT_MAX)) (PreH2 : (cells >= 0)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (S >= INT_MIN)) (PreH11 : (q_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (j <= n_pre)) (PreH14 : (S = (n_pre + 1 ))) (PreH15 : (cells = (S * S ))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (1 <= q_pre)) (PreH19 : (q_pre <= 1000000)) (PreH20 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH21 : ((Zlength (queries_data)) = q_pre)) (PreH22 : (MatrixValuesBounded matrix_data n_pre )) (PreH23 : (QueriesBounded queries_data n_pre )) (PreH24 : (RawQueriesEncode queries_data raw_queries )) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= (n_pre + 1 ))) (PreH29 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  TT && emp 
|--
  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ”
  &&  emp
).

Definition solver_entail_wit_3_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (cells <= UINT_MAX)) (PreH2 : (cells >= 0)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (S >= INT_MIN)) (PreH11 : (q_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (j <= n_pre)) (PreH14 : (S = (n_pre + 1 ))) (PreH15 : (cells = (S * S ))) (PreH16 : (1 <= n_pre)) (PreH17 : (n_pre <= 2000)) (PreH18 : (1 <= q_pre)) (PreH19 : (q_pre <= 1000000)) (PreH20 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH21 : ((Zlength (queries_data)) = q_pre)) (PreH22 : (MatrixValuesBounded matrix_data n_pre )) (PreH23 : (QueriesBounded queries_data n_pre )) (PreH24 : (RawQueriesEncode queries_data raw_queries )) (PreH25 : (1 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (1 <= j)) (PreH28 : (j <= (n_pre + 1 ))) (PreH29 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))
.

Definition solver_entail_wit_4 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH2 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (S >= INT_MIN)) (PreH8 : (q_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  ((( &( "z" ) )) # UInt  |-> ((i * S ) + j ))
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  ((( &( "x" ) )) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH2 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH3 : (((i * S ) + j ) <= UINT_MAX)) (PreH4 : (((i * S ) + j ) >= 0)) (PreH5 : (j <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH12 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH13 : (cells <= UINT_MAX)) (PreH14 : (cells >= 0)) (PreH15 : (S <= INT_MAX)) (PreH16 : (q_pre <= INT_MAX)) (PreH17 : (S >= INT_MIN)) (PreH18 : (q_pre >= INT_MIN)) (PreH19 : (j <= n_pre)) (PreH20 : (S = (n_pre + 1 ))) (PreH21 : (cells = (S * S ))) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 2000)) (PreH24 : (1 <= q_pre)) (PreH25 : (q_pre <= 1000000)) (PreH26 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH27 : ((Zlength (queries_data)) = q_pre)) (PreH28 : (MatrixValuesBounded matrix_data n_pre )) (PreH29 : (QueriesBounded queries_data n_pre )) (PreH30 : (RawQueriesEncode queries_data raw_queries )) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  TT && emp 
|--
  “ (((i * (n_pre + 1 ) ) + j ) < (S * S )) ” 
  &&  “ ((((i * (n_pre + 1 ) ) + j ) - 1 ) < (S * S )) ” 
  &&  “ ((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) < (S * S )) ” 
  &&  “ (((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) - 1 ) < (S * S )) ”
  &&  emp
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH2 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH3 : (((i * S ) + j ) <= UINT_MAX)) (PreH4 : (((i * S ) + j ) >= 0)) (PreH5 : (j <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH12 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH13 : (cells <= UINT_MAX)) (PreH14 : (cells >= 0)) (PreH15 : (S <= INT_MAX)) (PreH16 : (q_pre <= INT_MAX)) (PreH17 : (S >= INT_MIN)) (PreH18 : (q_pre >= INT_MIN)) (PreH19 : (j <= n_pre)) (PreH20 : (S = (n_pre + 1 ))) (PreH21 : (cells = (S * S ))) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 2000)) (PreH24 : (1 <= q_pre)) (PreH25 : (q_pre <= 1000000)) (PreH26 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH27 : ((Zlength (queries_data)) = q_pre)) (PreH28 : (MatrixValuesBounded matrix_data n_pre )) (PreH29 : (QueriesBounded queries_data n_pre )) (PreH30 : (RawQueriesEncode queries_data raw_queries )) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (((i * (n_pre + 1 ) ) + j ) < (S * S ))
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH2 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH3 : (((i * S ) + j ) <= UINT_MAX)) (PreH4 : (((i * S ) + j ) >= 0)) (PreH5 : (j <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH12 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH13 : (cells <= UINT_MAX)) (PreH14 : (cells >= 0)) (PreH15 : (S <= INT_MAX)) (PreH16 : (q_pre <= INT_MAX)) (PreH17 : (S >= INT_MIN)) (PreH18 : (q_pre >= INT_MIN)) (PreH19 : (j <= n_pre)) (PreH20 : (S = (n_pre + 1 ))) (PreH21 : (cells = (S * S ))) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 2000)) (PreH24 : (1 <= q_pre)) (PreH25 : (q_pre <= 1000000)) (PreH26 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH27 : ((Zlength (queries_data)) = q_pre)) (PreH28 : (MatrixValuesBounded matrix_data n_pre )) (PreH29 : (QueriesBounded queries_data n_pre )) (PreH30 : (RawQueriesEncode queries_data raw_queries )) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((((i * (n_pre + 1 ) ) + j ) - 1 ) < (S * S ))
.

Definition solver_entail_wit_4_split_goal_3 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH2 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH3 : (((i * S ) + j ) <= UINT_MAX)) (PreH4 : (((i * S ) + j ) >= 0)) (PreH5 : (j <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH12 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH13 : (cells <= UINT_MAX)) (PreH14 : (cells >= 0)) (PreH15 : (S <= INT_MAX)) (PreH16 : (q_pre <= INT_MAX)) (PreH17 : (S >= INT_MIN)) (PreH18 : (q_pre >= INT_MIN)) (PreH19 : (j <= n_pre)) (PreH20 : (S = (n_pre + 1 ))) (PreH21 : (cells = (S * S ))) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 2000)) (PreH24 : (1 <= q_pre)) (PreH25 : (q_pre <= 1000000)) (PreH26 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH27 : ((Zlength (queries_data)) = q_pre)) (PreH28 : (MatrixValuesBounded matrix_data n_pre )) (PreH29 : (QueriesBounded queries_data n_pre )) (PreH30 : (RawQueriesEncode queries_data raw_queries )) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  ((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) < (S * S ))
.

Definition solver_entail_wit_4_split_goal_4 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH2 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH3 : (((i * S ) + j ) <= UINT_MAX)) (PreH4 : (((i * S ) + j ) >= 0)) (PreH5 : (j <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (n_pre >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH12 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH13 : (cells <= UINT_MAX)) (PreH14 : (cells >= 0)) (PreH15 : (S <= INT_MAX)) (PreH16 : (q_pre <= INT_MAX)) (PreH17 : (S >= INT_MIN)) (PreH18 : (q_pre >= INT_MIN)) (PreH19 : (j <= n_pre)) (PreH20 : (S = (n_pre + 1 ))) (PreH21 : (cells = (S * S ))) (PreH22 : (1 <= n_pre)) (PreH23 : (n_pre <= 2000)) (PreH24 : (1 <= q_pre)) (PreH25 : (q_pre <= 1000000)) (PreH26 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH27 : ((Zlength (queries_data)) = q_pre)) (PreH28 : (MatrixValuesBounded matrix_data n_pre )) (PreH29 : (QueriesBounded queries_data n_pre )) (PreH30 : (RawQueriesEncode queries_data raw_queries )) (PreH31 : (1 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (1 <= j)) (PreH34 : (j <= (n_pre + 1 ))) (PreH35 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) - 1 ) < (S * S ))
.

Definition solver_entail_wit_5 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (j > n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= (n_pre + 1 ))) (PreH17 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l_2 )
  **  (Int64Array.full row (S * S ) row_l_2 )
  **  (Int64Array.full col (S * S ) col_l_2 )
|--
  EX (sum_l: (@list Z))  (row_l: (@list Z))  (col_l: (@list Z)) ,
  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i + 1 ) * S ) ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (j > n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= (n_pre + 1 ))) (PreH17 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S ((i * S ) + j ) )) ,
  TT && emp 
|--
  “ (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre (n_pre + 1 ) ((i + 1 ) * (n_pre + 1 ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (j > n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (1 <= j)) (PreH16 : (j <= (n_pre + 1 ))) (PreH17 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S ((i * S ) + j ) )) ,
  (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre (n_pre + 1 ) ((i + 1 ) * (n_pre + 1 ) ) )
.

Definition solver_entail_wit_6 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * S ) + j ) - S ) col_l_2 0) ) + (Znth (((i * S ) + j ) - 1 ) col_l_2 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) col_l_2 0) )) (col_l_2)) )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l_2 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l_2 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l_2 0) )) (row_l_2)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l_2 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l_2 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l_2 0) )) (sum_l_2)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  EX (sum_l: (@list Z))  (row_l: (@list Z))  (col_l: (@list Z)) ,
  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + (j + 1 ) ) ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S ((i * S ) + j ) )) ,
  TT && emp 
|--
  “ (PrefixTables matrix_data (replace_Znth (((i * (n_pre + 1 ) ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) sum_l_2 0) ) + (Znth (((i * (n_pre + 1 ) ) + j ) - 1 ) sum_l_2 0) ) - (Znth ((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) - 1 ) sum_l_2 0) )) (sum_l_2)) (replace_Znth (((i * (n_pre + 1 ) ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) row_l_2 0) ) + (Znth (((i * (n_pre + 1 ) ) + j ) - 1 ) row_l_2 0) ) - (Znth ((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) - 1 ) row_l_2 0) )) (row_l_2)) (replace_Znth (((i * (n_pre + 1 ) ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) col_l_2 0) ) + (Znth (((i * (n_pre + 1 ) ) + j ) - 1 ) col_l_2 0) ) - (Znth ((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) - 1 ) col_l_2 0) )) (col_l_2)) n_pre (n_pre + 1 ) ((i * (n_pre + 1 ) ) + (j + 1 ) ) ) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S ((i * S ) + j ) )) ,
  (PrefixTables matrix_data (replace_Znth (((i * (n_pre + 1 ) ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) sum_l_2 0) ) + (Znth (((i * (n_pre + 1 ) ) + j ) - 1 ) sum_l_2 0) ) - (Znth ((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) - 1 ) sum_l_2 0) )) (sum_l_2)) (replace_Znth (((i * (n_pre + 1 ) ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) row_l_2 0) ) + (Znth (((i * (n_pre + 1 ) ) + j ) - 1 ) row_l_2 0) ) - (Znth ((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) - 1 ) row_l_2 0) )) (row_l_2)) (replace_Znth (((i * (n_pre + 1 ) ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * j ) + (Znth (((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) col_l_2 0) ) + (Znth (((i * (n_pre + 1 ) ) + j ) - 1 ) col_l_2 0) ) - (Znth ((((i * (n_pre + 1 ) ) + j ) - (n_pre + 1 ) ) - 1 ) col_l_2 0) )) (col_l_2)) n_pre (n_pre + 1 ) ((i * (n_pre + 1 ) ) + (j + 1 ) ) )
.

Definition solver_entail_wit_7 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i > n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S (i * S ) )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l_2 )
  **  (Int64Array.full row (S * S ) row_l_2 )
  **  (Int64Array.full col (S * S ) col_l_2 )
|--
  EX (sum_l: (@list Z))  (row_l: (@list Z))  (col_l: (@list Z)) ,
  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i > n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S (i * S ) )) ,
  TT && emp 
|--
  “ (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre (n_pre + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_7_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i > n_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (1 <= i)) (PreH14 : (i <= (n_pre + 1 ))) (PreH15 : (PrefixTables matrix_data sum_l_2 row_l_2 col_l_2 n_pre S (i * S ) )) ,
  (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre (n_pre + 1 ) )
.

Definition solver_entail_wit_8 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (S: Z) (cells: Z) (sum: Z) (row: Z) (col: Z) (PreH1 : (S = (n_pre + 1 ))) (PreH2 : (cells = (S * S ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 1000000)) (PreH7 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH8 : ((Zlength (queries_data)) = q_pre)) (PreH9 : (MatrixValuesBounded matrix_data n_pre )) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : (RawQueriesEncode queries_data raw_queries )) (PreH12 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l_2 )
  **  (Int64Array.full row (S * S ) row_l_2 )
  **  (Int64Array.full col (S * S ) col_l_2 )
|--
  EX (result: (@list Z))  (sum_l: (@list Z))  (row_l: (@list Z))  (col_l: (@list Z)) ,
  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= q_pre) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result 0 ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 0 result )
  **  (Int64Array.undef_seg out_pre 0 q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (S: Z) (cells: Z) (PreH1 : (S = (n_pre + 1 ))) (PreH2 : (cells = (S * S ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 1000000)) (PreH7 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH8 : ((Zlength (queries_data)) = q_pre)) (PreH9 : (MatrixValuesBounded matrix_data n_pre )) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : (RawQueriesEncode queries_data raw_queries )) (PreH12 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) ,
  TT && emp 
|--
  “ (OutputPrefix matrix_data n_pre queries_data (@nil Z) 0 ) ”
  &&  emp
).

Definition solver_entail_wit_8_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (S: Z) (cells: Z) (PreH1 : (S = (n_pre + 1 ))) (PreH2 : (cells = (S * S ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 1000000)) (PreH7 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH8 : ((Zlength (queries_data)) = q_pre)) (PreH9 : (MatrixValuesBounded matrix_data n_pre )) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : (RawQueriesEncode queries_data raw_queries )) (PreH12 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) ,
  (OutputPrefix matrix_data n_pre queries_data (@nil Z) 0 )
.

Definition solver_entail_wit_9 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result_2 )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l_2 )
  **  (Int64Array.full row (S * S ) row_l_2 )
  **  (Int64Array.full col (S * S ) col_l_2 )
|--
  EX (result: (@list Z))  (sum_l: (@list Z))  (row_l: (@list Z))  (col_l: (@list Z)) ,
  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < q_pre) ” 
  &&  “ ((Znth (4 * i ) raw_queries 0) = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ ((Znth ((4 * i ) + 1 ) raw_queries 0) = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ ((Znth ((4 * i ) + 2 ) raw_queries 0) = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ ((Znth ((4 * i ) + 3 ) raw_queries 0) = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (1 <= (Znth (4 * i ) raw_queries 0)) ” 
  &&  “ ((Znth (4 * i ) raw_queries 0) <= (Znth ((4 * i ) + 2 ) raw_queries 0)) ” 
  &&  “ ((Znth ((4 * i ) + 2 ) raw_queries 0) < S) ” 
  &&  “ (1 <= (Znth ((4 * i ) + 1 ) raw_queries 0)) ” 
  &&  “ ((Znth ((4 * i ) + 1 ) raw_queries 0) <= (Znth ((4 * i ) + 3 ) raw_queries 0)) ” 
  &&  “ ((Znth ((4 * i ) + 3 ) raw_queries 0) < S) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) ) ” 
  &&  “ (RectanglesBounded row_l S 4002000000000000 ) ” 
  &&  “ (RectanglesBounded col_l S 4002000000000000 ) ” 
  &&  “ (RectIntermediatesSafe sum_l S ) ” 
  &&  “ (RectIntermediatesSafe row_l S ) ” 
  &&  “ (RectIntermediatesSafe col_l S ) ” 
  &&  “ (QueryArithmeticSafe sum_l row_l col_l S (Znth (4 * i ) raw_queries 0) (Znth ((4 * i ) + 1 ) raw_queries 0) (Znth ((4 * i ) + 2 ) raw_queries 0) (Znth ((4 * i ) + 3 ) raw_queries 0) ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  TT && emp 
|--
  “ (QueryArithmeticSafe sum_l_2 row_l_2 col_l_2 (n_pre + 1 ) (Znth (4 * i ) raw_queries 0) (Znth ((4 * i ) + 1 ) raw_queries 0) (Znth ((4 * i ) + 2 ) raw_queries 0) (Znth ((4 * i ) + 3 ) raw_queries 0) ) ” 
  &&  “ (RectIntermediatesSafe col_l_2 (n_pre + 1 ) ) ” 
  &&  “ (RectIntermediatesSafe row_l_2 (n_pre + 1 ) ) ” 
  &&  “ (RectIntermediatesSafe sum_l_2 (n_pre + 1 ) ) ” 
  &&  “ (RectanglesBounded col_l_2 (n_pre + 1 ) 4002000000000000 ) ” 
  &&  “ (RectanglesBounded row_l_2 (n_pre + 1 ) 4002000000000000 ) ” 
  &&  “ (RectanglesBounded sum_l_2 (n_pre + 1 ) (4 * (Z.pow (10) (12)) ) ) ” 
  &&  “ ((Znth ((4 * i ) + 3 ) raw_queries 0) < (n_pre + 1 )) ” 
  &&  “ ((Znth ((4 * i ) + 1 ) raw_queries 0) <= (Znth ((4 * i ) + 3 ) raw_queries 0)) ” 
  &&  “ (1 <= (Znth ((4 * i ) + 1 ) raw_queries 0)) ” 
  &&  “ ((Znth ((4 * i ) + 2 ) raw_queries 0) < (n_pre + 1 )) ” 
  &&  “ ((Znth (4 * i ) raw_queries 0) <= (Znth ((4 * i ) + 2 ) raw_queries 0)) ” 
  &&  “ (1 <= (Znth (4 * i ) raw_queries 0)) ” 
  &&  “ ((Znth ((4 * i ) + 3 ) raw_queries 0) = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ ((Znth ((4 * i ) + 2 ) raw_queries 0) = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ ((Znth ((4 * i ) + 1 ) raw_queries 0) = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ ((Znth (4 * i ) raw_queries 0) = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (QueryArithmeticSafe sum_l_2 row_l_2 col_l_2 (n_pre + 1 ) (Znth (4 * i ) raw_queries 0) (Znth ((4 * i ) + 1 ) raw_queries 0) (Znth ((4 * i ) + 2 ) raw_queries 0) (Znth ((4 * i ) + 3 ) raw_queries 0) )
.

Definition solver_entail_wit_9_split_goal_2 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (RectIntermediatesSafe col_l_2 (n_pre + 1 ) )
.

Definition solver_entail_wit_9_split_goal_3 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (RectIntermediatesSafe row_l_2 (n_pre + 1 ) )
.

Definition solver_entail_wit_9_split_goal_4 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (RectIntermediatesSafe sum_l_2 (n_pre + 1 ) )
.

Definition solver_entail_wit_9_split_goal_5 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (RectanglesBounded col_l_2 (n_pre + 1 ) 4002000000000000 )
.

Definition solver_entail_wit_9_split_goal_6 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (RectanglesBounded row_l_2 (n_pre + 1 ) 4002000000000000 )
.

Definition solver_entail_wit_9_split_goal_7 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (RectanglesBounded sum_l_2 (n_pre + 1 ) (4 * (Z.pow (10) (12)) ) )
.

Definition solver_entail_wit_9_split_goal_8 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  ((Znth ((4 * i ) + 3 ) raw_queries 0) < (n_pre + 1 ))
.

Definition solver_entail_wit_9_split_goal_9 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  ((Znth ((4 * i ) + 1 ) raw_queries 0) <= (Znth ((4 * i ) + 3 ) raw_queries 0))
.

Definition solver_entail_wit_9_split_goal_10 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (1 <= (Znth ((4 * i ) + 1 ) raw_queries 0))
.

Definition solver_entail_wit_9_split_goal_11 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  ((Znth ((4 * i ) + 2 ) raw_queries 0) < (n_pre + 1 ))
.

Definition solver_entail_wit_9_split_goal_12 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  ((Znth (4 * i ) raw_queries 0) <= (Znth ((4 * i ) + 2 ) raw_queries 0))
.

Definition solver_entail_wit_9_split_goal_13 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (1 <= (Znth (4 * i ) raw_queries 0))
.

Definition solver_entail_wit_9_split_goal_14 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  ((Znth ((4 * i ) + 3 ) raw_queries 0) = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))
.

Definition solver_entail_wit_9_split_goal_15 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  ((Znth ((4 * i ) + 2 ) raw_queries 0) = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))
.

Definition solver_entail_wit_9_split_goal_16 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  ((Znth ((4 * i ) + 1 ) raw_queries 0) = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))
.

Definition solver_entail_wit_9_split_goal_17 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (i: Z) (cells: Z) (S: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  ((Znth (4 * i ) raw_queries 0) = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))
.

Definition solver_entail_wit_10 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (result_2: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l_2) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l_2) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l_2) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH34 : (RectanglesBounded sum_l_2 S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l_2 S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l_2 S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l_2 S )) (PreH38 : (RectIntermediatesSafe row_l_2 S )) (PreH39 : (RectIntermediatesSafe col_l_2 S )) (PreH40 : (QueryArithmeticSafe sum_l_2 row_l_2 col_l_2 S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (Int64Array.seg out_pre 0 (i + 1 ) (app (result_2) ((cons ((((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) )) ((@nil Z))))) )
  **  (Int64Array.undef_seg out_pre (i + 1 ) q_pre )
  **  (Int64Array.full col (S * S ) col_l_2 )
  **  (Int64Array.full row (S * S ) row_l_2 )
  **  (Int64Array.full sum (S * S ) sum_l_2 )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
|--
  EX (result: (@list Z))  (sum_l: (@list Z))  (row_l: (@list Z))  (col_l: (@list Z)) ,
  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= q_pre) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result (i + 1 ) ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 (i + 1 ) result )
  **  (Int64Array.undef_seg out_pre (i + 1 ) q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
) \/
(
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (result_2: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l_2) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l_2) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l_2) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH34 : (RectanglesBounded sum_l_2 S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l_2 S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l_2 S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l_2 S )) (PreH38 : (RectIntermediatesSafe row_l_2 S )) (PreH39 : (RectIntermediatesSafe col_l_2 S )) (PreH40 : (QueryArithmeticSafe sum_l_2 row_l_2 col_l_2 S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  TT && emp 
|--
  “ (OutputPrefix matrix_data n_pre queries_data (app (result_2) ((cons ((((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) )) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp
).

Definition solver_entail_wit_10_split_goal_1 := 
forall (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l_2: (@list Z)) (row_l_2: (@list Z)) (col_l_2: (@list Z)) (result_2: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l_2) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l_2) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l_2) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l_2 row_l_2 col_l_2 n_pre S )) (PreH34 : (RectanglesBounded sum_l_2 S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l_2 S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l_2 S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l_2 S )) (PreH38 : (RectIntermediatesSafe row_l_2 S )) (PreH39 : (RectIntermediatesSafe col_l_2 S )) (PreH40 : (QueryArithmeticSafe sum_l_2 row_l_2 col_l_2 S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (OutputPrefix matrix_data n_pre queries_data (app (result_2) ((cons ((((((y2 - y1 ) + 1 ) * (retval_2 - (x1 * retval ) ) ) + retval_3 ) - ((y1 - 1 ) * retval ) )) ((@nil Z))))) (i + 1 ) )
.

Definition solver_return_wit_1 := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i >= q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result_2 )
|--
  EX (result: (@list Z)) ,
  “ (Spec matrix_data n_pre queries_data result ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.full out_pre q_pre result )
) \/
(
forall (out_pre: Z) (q_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (result_2: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i >= q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result_2 i )) ,
  (Int64Array.seg out_pre 0 i result_2 )
|--
  EX (result: (@list Z)) ,
  “ (Spec matrix_data n_pre queries_data result ) ”
  &&  (Int64Array.full out_pre q_pre result )
).

Definition solver_partial_solve_wit_1_pure := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z))  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000)) (PreH3 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH4 : (MatrixValuesBounded matrix_data n_pre )) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 1000000)) (PreH7 : (QueriesBounded queries_data n_pre )) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH9 : (q_pre = (Zlength (queries_data)))) (PreH10 : (RawQueriesEncode queries_data raw_queries )) ,
  ((( &( "sum" ) )) # Ptr  |->_)
  **  ((( &( "cells" ) )) # UInt  |-> ((n_pre + 1 ) * (n_pre + 1 ) ))
  **  ((( &( "S" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (0 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (((n_pre + 1 ) * (n_pre + 1 ) ) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z))  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 2000)) (PreH3 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH4 : (MatrixValuesBounded matrix_data n_pre )) (PreH5 : (1 <= (Zlength (queries_data)))) (PreH6 : ((Zlength (queries_data)) <= 1000000)) (PreH7 : (QueriesBounded queries_data n_pre )) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH9 : (q_pre = (Zlength (queries_data)))) (PreH10 : (RawQueriesEncode queries_data raw_queries )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (0 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (((n_pre + 1 ) * (n_pre + 1 ) ) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 1000000) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ”
  &&  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (retval: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH5 : (MatrixValuesBounded matrix_data n_pre )) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 1000000)) (PreH8 : (QueriesBounded queries_data n_pre )) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH10 : (q_pre = (Zlength (queries_data)))) (PreH11 : (RawQueriesEncode queries_data raw_queries )) ,
  ((( &( "row" ) )) # Ptr  |->_)
  **  (Int64Array.full retval ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  ((( &( "sum" ) )) # Ptr  |-> retval)
  **  ((( &( "cells" ) )) # UInt  |-> ((n_pre + 1 ) * (n_pre + 1 ) ))
  **  ((( &( "S" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (0 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (((n_pre + 1 ) * (n_pre + 1 ) ) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (retval: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 2000)) (PreH4 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH5 : (MatrixValuesBounded matrix_data n_pre )) (PreH6 : (1 <= (Zlength (queries_data)))) (PreH7 : ((Zlength (queries_data)) <= 1000000)) (PreH8 : (QueriesBounded queries_data n_pre )) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH10 : (q_pre = (Zlength (queries_data)))) (PreH11 : (RawQueriesEncode queries_data raw_queries )) ,
  (Int64Array.full retval ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (0 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (((n_pre + 1 ) * (n_pre + 1 ) ) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 1000000) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ”
  &&  (Int64Array.full retval ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3_pure := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (retval: Z) (retval_2: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH6 : (MatrixValuesBounded matrix_data n_pre )) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 1000000)) (PreH9 : (QueriesBounded queries_data n_pre )) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH11 : (q_pre = (Zlength (queries_data)))) (PreH12 : (RawQueriesEncode queries_data raw_queries )) ,
  ((( &( "col" ) )) # Ptr  |->_)
  **  (Int64Array.full retval_2 ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  ((( &( "row" ) )) # Ptr  |-> retval_2)
  **  (Int64Array.full retval ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  ((( &( "sum" ) )) # Ptr  |-> retval)
  **  ((( &( "cells" ) )) # UInt  |-> ((n_pre + 1 ) * (n_pre + 1 ) ))
  **  ((( &( "S" ) )) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (0 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (((n_pre + 1 ) * (n_pre + 1 ) ) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ”
.

Definition solver_partial_solve_wit_3_aux := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (retval: Z) (retval_2: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH6 : (MatrixValuesBounded matrix_data n_pre )) (PreH7 : (1 <= (Zlength (queries_data)))) (PreH8 : ((Zlength (queries_data)) <= 1000000)) (PreH9 : (QueriesBounded queries_data n_pre )) (PreH10 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)))) (PreH11 : (q_pre = (Zlength (queries_data)))) (PreH12 : (RawQueriesEncode queries_data raw_queries )) ,
  (Int64Array.full retval_2 ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  (Int64Array.full retval ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (0 <= ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (((n_pre + 1 ) * (n_pre + 1 ) ) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (sizeof(INT64) = sizeof(INT64)) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (1 <= (Zlength (queries_data))) ” 
  &&  “ ((Zlength (queries_data)) <= 1000000) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (queries_data)))) -> (((((0 <= (zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))))) /\ ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre)) /\ ((0 <= (zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))) /\ ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) <= (zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z)))))) /\ ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) < n_pre))) ” 
  &&  “ (q_pre = (Zlength (queries_data))) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ”
  &&  (Int64Array.full retval_2 ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  (Int64Array.full retval ((n_pre + 1 ) * (n_pre + 1 ) ) (repeat_Z (0) (((n_pre + 1 ) * (n_pre + 1 ) ))) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH2 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (S <= INT_MAX)) (PreH6 : (q_pre <= INT_MAX)) (PreH7 : (S >= INT_MIN)) (PreH8 : (q_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1 ))) (PreH25 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((matrix_pre + (((((i - 1 ) * n_pre ) + j ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0))
  **  (Int64Array.missing_i matrix_pre ((((i - 1 ) * n_pre ) + j ) - 1 ) 0 (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_5 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((sum + ((((i * S ) + j ) - S ) * sizeof(INT64)))) # Int64  |-> (Znth (((i * S ) + j ) - S ) sum_l 0))
  **  (Int64Array.missing_i sum (((i * S ) + j ) - S ) 0 (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_6 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((sum + ((((i * S ) + j ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (((i * S ) + j ) - 1 ) sum_l 0))
  **  (Int64Array.missing_i sum (((i * S ) + j ) - 1 ) 0 (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_7 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((sum + (((((i * S ) + j ) - S ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0))
  **  (Int64Array.missing_i sum ((((i * S ) + j ) - S ) - 1 ) 0 (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_8 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((sum + (((i * S ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i sum ((i * S ) + j ) 0 (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_9 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((row + ((((i * S ) + j ) - S ) * sizeof(INT64)))) # Int64  |-> (Znth (((i * S ) + j ) - S ) row_l 0))
  **  (Int64Array.missing_i row (((i * S ) + j ) - S ) 0 (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_10 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((row + ((((i * S ) + j ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (((i * S ) + j ) - 1 ) row_l 0))
  **  (Int64Array.missing_i row (((i * S ) + j ) - 1 ) 0 (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_11 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((row + (((((i * S ) + j ) - S ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0))
  **  (Int64Array.missing_i row ((((i * S ) + j ) - S ) - 1 ) 0 (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_12 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((row + (((i * S ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i row ((i * S ) + j ) 0 (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_13 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((col + ((((i * S ) + j ) - S ) * sizeof(INT64)))) # Int64  |-> (Znth (((i * S ) + j ) - S ) col_l 0))
  **  (Int64Array.missing_i col (((i * S ) + j ) - S ) 0 (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_14 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((col + ((((i * S ) + j ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth (((i * S ) + j ) - 1 ) col_l 0))
  **  (Int64Array.missing_i col (((i * S ) + j ) - 1 ) 0 (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_15 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((col + (((((i * S ) + j ) - S ) - 1 ) * sizeof(INT64)))) # Int64  |-> (Znth ((((i * S ) + j ) - S ) - 1 ) col_l 0))
  **  (Int64Array.missing_i col ((((i * S ) + j ) - S ) - 1 ) 0 (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_16 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (j: Z) (i: Z) (cells: Z) (S: Z) (PreH1 : (0 <= ((((i * S ) + j ) - S ) - 1 ))) (PreH2 : (((((i * S ) + j ) - S ) - 1 ) < cells)) (PreH3 : (0 <= (((i * S ) + j ) - S ))) (PreH4 : ((((i * S ) + j ) - S ) < cells)) (PreH5 : (0 <= (((i * S ) + j ) - 1 ))) (PreH6 : ((((i * S ) + j ) - 1 ) < cells)) (PreH7 : (0 <= ((i * S ) + j ))) (PreH8 : (((i * S ) + j ) < cells)) (PreH9 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX)) (PreH10 : ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN)) (PreH11 : (j <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (i <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 ))) (PreH18 : (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre ))) (PreH19 : (cells <= UINT_MAX)) (PreH20 : (cells >= 0)) (PreH21 : (S <= INT_MAX)) (PreH22 : (q_pre <= INT_MAX)) (PreH23 : (S >= INT_MIN)) (PreH24 : (q_pre >= INT_MIN)) (PreH25 : (j <= n_pre)) (PreH26 : (S = (n_pre + 1 ))) (PreH27 : (cells = (S * S ))) (PreH28 : (1 <= n_pre)) (PreH29 : (n_pre <= 2000)) (PreH30 : (1 <= q_pre)) (PreH31 : (q_pre <= 1000000)) (PreH32 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH33 : ((Zlength (queries_data)) = q_pre)) (PreH34 : (MatrixValuesBounded matrix_data n_pre )) (PreH35 : (QueriesBounded queries_data n_pre )) (PreH36 : (RawQueriesEncode queries_data raw_queries )) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1 ))) (PreH41 : (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
|--
  “ (0 <= ((((i * S ) + j ) - S ) - 1 )) ” 
  &&  “ (((((i * S ) + j ) - S ) - 1 ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - S )) ” 
  &&  “ ((((i * S ) + j ) - S ) < cells) ” 
  &&  “ (0 <= (((i * S ) + j ) - 1 )) ” 
  &&  “ ((((i * S ) + j ) - 1 ) < cells) ” 
  &&  “ (0 <= ((i * S ) + j )) ” 
  &&  “ (((i * S ) + j ) < cells) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) <= INT64_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) >= INT64_MIN) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (0 <= ((((i - 1 ) * n_pre ) + j ) - 1 )) ” 
  &&  “ (((((i - 1 ) * n_pre ) + j ) - 1 ) < (n_pre * n_pre )) ” 
  &&  “ (cells <= UINT_MAX) ” 
  &&  “ (cells >= 0) ” 
  &&  “ (S <= INT_MAX) ” 
  &&  “ (q_pre <= INT_MAX) ” 
  &&  “ (S >= INT_MIN) ” 
  &&  “ (q_pre >= INT_MIN) ” 
  &&  “ (j <= n_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (n_pre + 1 )) ” 
  &&  “ (PrefixTables matrix_data sum_l row_l col_l n_pre S ((i * S ) + j ) ) ”
  &&  (((col + (((i * S ) + j ) * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.missing_i col ((i * S ) + j ) 0 (S * S ) col_l )
  **  (Int64Array.full row (S * S ) (replace_Znth (((i * S ) + j )) ((((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) * i ) + (Znth (((i * S ) + j ) - S ) row_l 0) ) + (Znth (((i * S ) + j ) - 1 ) row_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) row_l 0) )) (row_l)) )
  **  (Int64Array.full sum (S * S ) (replace_Znth (((i * S ) + j )) (((((Znth ((((i - 1 ) * n_pre ) + j ) - 1 ) matrix_data 0) + (Znth (((i * S ) + j ) - S ) sum_l 0) ) + (Znth (((i * S ) + j ) - 1 ) sum_l 0) ) - (Znth ((((i * S ) + j ) - S ) - 1 ) sum_l 0) )) (sum_l)) )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.undef_full out_pre q_pre )
.

Definition solver_partial_solve_wit_17 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (i < q_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (((queries_pre + (((4 * i ) + 3 ) * sizeof(INT)))) # Int  |-> (Znth ((4 * i ) + 3 ) raw_queries 0))
  **  (IntArray.missing_i queries_pre ((4 * i ) + 3 ) 0 (4 * q_pre ) raw_queries )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_18 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (i < q_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (((queries_pre + (((4 * i ) + 2 ) * sizeof(INT)))) # Int  |-> (Znth ((4 * i ) + 2 ) raw_queries 0))
  **  (IntArray.missing_i queries_pre ((4 * i ) + 2 ) 0 (4 * q_pre ) raw_queries )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_19 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (i < q_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (((queries_pre + (((4 * i ) + 1 ) * sizeof(INT)))) # Int  |-> (Znth ((4 * i ) + 1 ) raw_queries 0))
  **  (IntArray.missing_i queries_pre ((4 * i ) + 1 ) 0 (4 * q_pre ) raw_queries )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_20 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i < q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (i < q_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (((queries_pre + ((4 * i ) * sizeof(INT)))) # Int  |-> (Znth (4 * i ) raw_queries 0))
  **  (IntArray.missing_i queries_pre (4 * i ) 0 (4 * q_pre ) raw_queries )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_21_pure := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 4002000000000000)) (PreH4 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH7 : (S = (n_pre + 1 ))) (PreH8 : (cells = (S * S ))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 1000000)) (PreH13 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH14 : ((Zlength (queries_data)) = q_pre)) (PreH15 : (MatrixValuesBounded matrix_data n_pre )) (PreH16 : (QueriesBounded queries_data n_pre )) (PreH17 : (RawQueriesEncode queries_data raw_queries )) (PreH18 : (0 <= i)) (PreH19 : (i < q_pre)) (PreH20 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH21 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH22 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH23 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (1 <= x1)) (PreH25 : (x1 <= x2)) (PreH26 : (x2 < S)) (PreH27 : (1 <= y1)) (PreH28 : (y1 <= y2)) (PreH29 : (y2 < S)) (PreH30 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH31 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH32 : (RectanglesBounded row_l S 4002000000000000 )) (PreH33 : (RectanglesBounded col_l S 4002000000000000 )) (PreH34 : (RectIntermediatesSafe sum_l S )) (PreH35 : (RectIntermediatesSafe row_l S )) (PreH36 : (RectIntermediatesSafe col_l S )) (PreH37 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH38 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "cs" ) )) # Int64  |->_)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (2 <= S) ” 
  &&  “ (S <= 2001) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ (0 <= 4002000000000000) ” 
  &&  “ (4002000000000000 <= 4002000000000000) ” 
  &&  “ ((Zlength (col_l)) = (S * S )) ” 
  &&  “ (RectanglesBounded col_l S 4002000000000000 ) ” 
  &&  “ (RectIntermediatesSafe col_l S ) ” 
  &&  “ ((Zlength (col_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval_2 <= INT64_MAX)) (PreH3 : (retval >= INT64_MIN)) (PreH4 : (retval_2 >= INT64_MIN)) (PreH5 : (cells <= UINT_MAX)) (PreH6 : (cells >= 0)) (PreH7 : (y2 <= INT_MAX)) (PreH8 : (x2 <= INT_MAX)) (PreH9 : (y1 <= INT_MAX)) (PreH10 : (x1 <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (S <= INT_MAX)) (PreH13 : (q_pre <= INT_MAX)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (y2 >= INT_MIN)) (PreH16 : (x2 >= INT_MIN)) (PreH17 : (y1 >= INT_MIN)) (PreH18 : (x1 >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (S >= INT_MIN)) (PreH21 : (q_pre >= INT_MIN)) (PreH22 : (n_pre >= INT_MIN)) (PreH23 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 4002000000000000)) (PreH26 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH27 : (0 <= retval)) (PreH28 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH29 : (S = (n_pre + 1 ))) (PreH30 : (cells = (S * S ))) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= q_pre)) (PreH34 : (q_pre <= 1000000)) (PreH35 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH36 : ((Zlength (queries_data)) = q_pre)) (PreH37 : (MatrixValuesBounded matrix_data n_pre )) (PreH38 : (QueriesBounded queries_data n_pre )) (PreH39 : (RawQueriesEncode queries_data raw_queries )) (PreH40 : (0 <= i)) (PreH41 : (i < q_pre)) (PreH42 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH43 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH44 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH45 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH46 : (1 <= x1)) (PreH47 : (x1 <= x2)) (PreH48 : (x2 < S)) (PreH49 : (1 <= y1)) (PreH50 : (y1 <= y2)) (PreH51 : (y2 < S)) (PreH52 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH53 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH54 : (RectanglesBounded row_l S 4002000000000000 )) (PreH55 : (RectanglesBounded col_l S 4002000000000000 )) (PreH56 : (RectIntermediatesSafe sum_l S )) (PreH57 : (RectIntermediatesSafe row_l S )) (PreH58 : (RectIntermediatesSafe col_l S )) (PreH59 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH60 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "cs" ) )) # Int64  |->_)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((Zlength (col_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (col_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
).

Definition solver_partial_solve_wit_21_pure_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval_2 <= INT64_MAX)) (PreH3 : (retval >= INT64_MIN)) (PreH4 : (retval_2 >= INT64_MIN)) (PreH5 : (cells <= UINT_MAX)) (PreH6 : (cells >= 0)) (PreH7 : (y2 <= INT_MAX)) (PreH8 : (x2 <= INT_MAX)) (PreH9 : (y1 <= INT_MAX)) (PreH10 : (x1 <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (S <= INT_MAX)) (PreH13 : (q_pre <= INT_MAX)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (y2 >= INT_MIN)) (PreH16 : (x2 >= INT_MIN)) (PreH17 : (y1 >= INT_MIN)) (PreH18 : (x1 >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (S >= INT_MIN)) (PreH21 : (q_pre >= INT_MIN)) (PreH22 : (n_pre >= INT_MIN)) (PreH23 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 4002000000000000)) (PreH26 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH27 : (0 <= retval)) (PreH28 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH29 : (S = (n_pre + 1 ))) (PreH30 : (cells = (S * S ))) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= q_pre)) (PreH34 : (q_pre <= 1000000)) (PreH35 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH36 : ((Zlength (queries_data)) = q_pre)) (PreH37 : (MatrixValuesBounded matrix_data n_pre )) (PreH38 : (QueriesBounded queries_data n_pre )) (PreH39 : (RawQueriesEncode queries_data raw_queries )) (PreH40 : (0 <= i)) (PreH41 : (i < q_pre)) (PreH42 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH43 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH44 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH45 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH46 : (1 <= x1)) (PreH47 : (x1 <= x2)) (PreH48 : (x2 < S)) (PreH49 : (1 <= y1)) (PreH50 : (y1 <= y2)) (PreH51 : (y2 < S)) (PreH52 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH53 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH54 : (RectanglesBounded row_l S 4002000000000000 )) (PreH55 : (RectanglesBounded col_l S 4002000000000000 )) (PreH56 : (RectIntermediatesSafe sum_l S )) (PreH57 : (RectIntermediatesSafe row_l S )) (PreH58 : (RectIntermediatesSafe col_l S )) (PreH59 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH60 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "cs" ) )) # Int64  |->_)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((Zlength (col_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
.

Definition solver_partial_solve_wit_21_pure_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval_2 <= INT64_MAX)) (PreH3 : (retval >= INT64_MIN)) (PreH4 : (retval_2 >= INT64_MIN)) (PreH5 : (cells <= UINT_MAX)) (PreH6 : (cells >= 0)) (PreH7 : (y2 <= INT_MAX)) (PreH8 : (x2 <= INT_MAX)) (PreH9 : (y1 <= INT_MAX)) (PreH10 : (x1 <= INT_MAX)) (PreH11 : (i <= INT_MAX)) (PreH12 : (S <= INT_MAX)) (PreH13 : (q_pre <= INT_MAX)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (y2 >= INT_MIN)) (PreH16 : (x2 >= INT_MIN)) (PreH17 : (y1 >= INT_MIN)) (PreH18 : (x1 >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (S >= INT_MIN)) (PreH21 : (q_pre >= INT_MIN)) (PreH22 : (n_pre >= INT_MIN)) (PreH23 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH24 : (0 <= retval_2)) (PreH25 : (retval_2 <= 4002000000000000)) (PreH26 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH27 : (0 <= retval)) (PreH28 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH29 : (S = (n_pre + 1 ))) (PreH30 : (cells = (S * S ))) (PreH31 : (1 <= n_pre)) (PreH32 : (n_pre <= 2000)) (PreH33 : (1 <= q_pre)) (PreH34 : (q_pre <= 1000000)) (PreH35 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH36 : ((Zlength (queries_data)) = q_pre)) (PreH37 : (MatrixValuesBounded matrix_data n_pre )) (PreH38 : (QueriesBounded queries_data n_pre )) (PreH39 : (RawQueriesEncode queries_data raw_queries )) (PreH40 : (0 <= i)) (PreH41 : (i < q_pre)) (PreH42 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH43 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH44 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH45 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH46 : (1 <= x1)) (PreH47 : (x1 <= x2)) (PreH48 : (x2 < S)) (PreH49 : (1 <= y1)) (PreH50 : (y1 <= y2)) (PreH51 : (y2 < S)) (PreH52 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH53 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH54 : (RectanglesBounded row_l S 4002000000000000 )) (PreH55 : (RectanglesBounded col_l S 4002000000000000 )) (PreH56 : (RectIntermediatesSafe sum_l S )) (PreH57 : (RectIntermediatesSafe row_l S )) (PreH58 : (RectIntermediatesSafe col_l S )) (PreH59 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH60 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "cs" ) )) # Int64  |->_)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "rs" ) )) # Int64  |-> retval_2)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((Zlength (col_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
.

Definition solver_partial_solve_wit_21_aux := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 <= 4002000000000000)) (PreH4 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval)) (PreH6 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH7 : (S = (n_pre + 1 ))) (PreH8 : (cells = (S * S ))) (PreH9 : (1 <= n_pre)) (PreH10 : (n_pre <= 2000)) (PreH11 : (1 <= q_pre)) (PreH12 : (q_pre <= 1000000)) (PreH13 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH14 : ((Zlength (queries_data)) = q_pre)) (PreH15 : (MatrixValuesBounded matrix_data n_pre )) (PreH16 : (QueriesBounded queries_data n_pre )) (PreH17 : (RawQueriesEncode queries_data raw_queries )) (PreH18 : (0 <= i)) (PreH19 : (i < q_pre)) (PreH20 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH21 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH22 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH23 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (1 <= x1)) (PreH25 : (x1 <= x2)) (PreH26 : (x2 < S)) (PreH27 : (1 <= y1)) (PreH28 : (y1 <= y2)) (PreH29 : (y2 < S)) (PreH30 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH31 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH32 : (RectanglesBounded row_l S 4002000000000000 )) (PreH33 : (RectanglesBounded col_l S 4002000000000000 )) (PreH34 : (RectIntermediatesSafe sum_l S )) (PreH35 : (RectIntermediatesSafe row_l S )) (PreH36 : (RectIntermediatesSafe col_l S )) (PreH37 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH38 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (2 <= S) ” 
  &&  “ (S <= 2001) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ (0 <= 4002000000000000) ” 
  &&  “ (4002000000000000 <= 4002000000000000) ” 
  &&  “ ((Zlength (col_l)) = (S * S )) ” 
  &&  “ (RectanglesBounded col_l S 4002000000000000 ) ” 
  &&  “ (RectIntermediatesSafe col_l S ) ” 
  &&  “ ((Zlength (col_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 4002000000000000) ” 
  &&  “ (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= (4 * (Z.pow (10) (12)) )) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) ) ” 
  &&  “ (RectanglesBounded row_l S 4002000000000000 ) ” 
  &&  “ (RectanglesBounded col_l S 4002000000000000 ) ” 
  &&  “ (RectIntermediatesSafe sum_l S ) ” 
  &&  “ (RectIntermediatesSafe row_l S ) ” 
  &&  “ (RectIntermediatesSafe col_l S ) ” 
  &&  “ (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
.

Definition solver_partial_solve_wit_21 := solver_partial_solve_wit_21_pure -> solver_partial_solve_wit_21_aux.

Definition solver_partial_solve_wit_22_pure := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH4 : (S = (n_pre + 1 ))) (PreH5 : (cells = (S * S ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 1000000)) (PreH10 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH11 : ((Zlength (queries_data)) = q_pre)) (PreH12 : (MatrixValuesBounded matrix_data n_pre )) (PreH13 : (QueriesBounded queries_data n_pre )) (PreH14 : (RawQueriesEncode queries_data raw_queries )) (PreH15 : (0 <= i)) (PreH16 : (i < q_pre)) (PreH17 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH18 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH19 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH20 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH21 : (1 <= x1)) (PreH22 : (x1 <= x2)) (PreH23 : (x2 < S)) (PreH24 : (1 <= y1)) (PreH25 : (y1 <= y2)) (PreH26 : (y2 < S)) (PreH27 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH28 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH29 : (RectanglesBounded row_l S 4002000000000000 )) (PreH30 : (RectanglesBounded col_l S 4002000000000000 )) (PreH31 : (RectIntermediatesSafe sum_l S )) (PreH32 : (RectIntermediatesSafe row_l S )) (PreH33 : (RectIntermediatesSafe col_l S )) (PreH34 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH35 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "rs" ) )) # Int64  |->_)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (2 <= S) ” 
  &&  “ (S <= 2001) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ (0 <= 4002000000000000) ” 
  &&  “ (4002000000000000 <= 4002000000000000) ” 
  &&  “ ((Zlength (row_l)) = (S * S )) ” 
  &&  “ (RectanglesBounded row_l S 4002000000000000 ) ” 
  &&  “ (RectIntermediatesSafe row_l S ) ” 
  &&  “ ((Zlength (row_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (y2 <= INT_MAX)) (PreH6 : (x2 <= INT_MAX)) (PreH7 : (y1 <= INT_MAX)) (PreH8 : (x1 <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (S <= INT_MAX)) (PreH11 : (q_pre <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (y2 >= INT_MIN)) (PreH14 : (x2 >= INT_MIN)) (PreH15 : (y1 >= INT_MIN)) (PreH16 : (x1 >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (S >= INT_MIN)) (PreH19 : (q_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH22 : (0 <= retval)) (PreH23 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH24 : (S = (n_pre + 1 ))) (PreH25 : (cells = (S * S ))) (PreH26 : (1 <= n_pre)) (PreH27 : (n_pre <= 2000)) (PreH28 : (1 <= q_pre)) (PreH29 : (q_pre <= 1000000)) (PreH30 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH31 : ((Zlength (queries_data)) = q_pre)) (PreH32 : (MatrixValuesBounded matrix_data n_pre )) (PreH33 : (QueriesBounded queries_data n_pre )) (PreH34 : (RawQueriesEncode queries_data raw_queries )) (PreH35 : (0 <= i)) (PreH36 : (i < q_pre)) (PreH37 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH38 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH39 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH40 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH41 : (1 <= x1)) (PreH42 : (x1 <= x2)) (PreH43 : (x2 < S)) (PreH44 : (1 <= y1)) (PreH45 : (y1 <= y2)) (PreH46 : (y2 < S)) (PreH47 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH48 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH49 : (RectanglesBounded row_l S 4002000000000000 )) (PreH50 : (RectanglesBounded col_l S 4002000000000000 )) (PreH51 : (RectIntermediatesSafe sum_l S )) (PreH52 : (RectIntermediatesSafe row_l S )) (PreH53 : (RectIntermediatesSafe col_l S )) (PreH54 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH55 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "rs" ) )) # Int64  |->_)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((Zlength (row_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (row_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
).

Definition solver_partial_solve_wit_22_pure_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (y2 <= INT_MAX)) (PreH6 : (x2 <= INT_MAX)) (PreH7 : (y1 <= INT_MAX)) (PreH8 : (x1 <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (S <= INT_MAX)) (PreH11 : (q_pre <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (y2 >= INT_MIN)) (PreH14 : (x2 >= INT_MIN)) (PreH15 : (y1 >= INT_MIN)) (PreH16 : (x1 >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (S >= INT_MIN)) (PreH19 : (q_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH22 : (0 <= retval)) (PreH23 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH24 : (S = (n_pre + 1 ))) (PreH25 : (cells = (S * S ))) (PreH26 : (1 <= n_pre)) (PreH27 : (n_pre <= 2000)) (PreH28 : (1 <= q_pre)) (PreH29 : (q_pre <= 1000000)) (PreH30 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH31 : ((Zlength (queries_data)) = q_pre)) (PreH32 : (MatrixValuesBounded matrix_data n_pre )) (PreH33 : (QueriesBounded queries_data n_pre )) (PreH34 : (RawQueriesEncode queries_data raw_queries )) (PreH35 : (0 <= i)) (PreH36 : (i < q_pre)) (PreH37 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH38 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH39 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH40 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH41 : (1 <= x1)) (PreH42 : (x1 <= x2)) (PreH43 : (x2 < S)) (PreH44 : (1 <= y1)) (PreH45 : (y1 <= y2)) (PreH46 : (y2 < S)) (PreH47 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH48 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH49 : (RectanglesBounded row_l S 4002000000000000 )) (PreH50 : (RectanglesBounded col_l S 4002000000000000 )) (PreH51 : (RectIntermediatesSafe sum_l S )) (PreH52 : (RectIntermediatesSafe row_l S )) (PreH53 : (RectIntermediatesSafe col_l S )) (PreH54 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH55 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "rs" ) )) # Int64  |->_)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((Zlength (row_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
.

Definition solver_partial_solve_wit_22_pure_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval <= INT64_MAX)) (PreH2 : (retval >= INT64_MIN)) (PreH3 : (cells <= UINT_MAX)) (PreH4 : (cells >= 0)) (PreH5 : (y2 <= INT_MAX)) (PreH6 : (x2 <= INT_MAX)) (PreH7 : (y1 <= INT_MAX)) (PreH8 : (x1 <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (S <= INT_MAX)) (PreH11 : (q_pre <= INT_MAX)) (PreH12 : (n_pre <= INT_MAX)) (PreH13 : (y2 >= INT_MIN)) (PreH14 : (x2 >= INT_MIN)) (PreH15 : (y1 >= INT_MIN)) (PreH16 : (x1 >= INT_MIN)) (PreH17 : (i >= INT_MIN)) (PreH18 : (S >= INT_MIN)) (PreH19 : (q_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH22 : (0 <= retval)) (PreH23 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH24 : (S = (n_pre + 1 ))) (PreH25 : (cells = (S * S ))) (PreH26 : (1 <= n_pre)) (PreH27 : (n_pre <= 2000)) (PreH28 : (1 <= q_pre)) (PreH29 : (q_pre <= 1000000)) (PreH30 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH31 : ((Zlength (queries_data)) = q_pre)) (PreH32 : (MatrixValuesBounded matrix_data n_pre )) (PreH33 : (QueriesBounded queries_data n_pre )) (PreH34 : (RawQueriesEncode queries_data raw_queries )) (PreH35 : (0 <= i)) (PreH36 : (i < q_pre)) (PreH37 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH38 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH39 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH40 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH41 : (1 <= x1)) (PreH42 : (x1 <= x2)) (PreH43 : (x2 < S)) (PreH44 : (1 <= y1)) (PreH45 : (y1 <= y2)) (PreH46 : (y2 < S)) (PreH47 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH48 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH49 : (RectanglesBounded row_l S 4002000000000000 )) (PreH50 : (RectanglesBounded col_l S 4002000000000000 )) (PreH51 : (RectIntermediatesSafe sum_l S )) (PreH52 : (RectIntermediatesSafe row_l S )) (PreH53 : (RectIntermediatesSafe col_l S )) (PreH54 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH55 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "rs" ) )) # Int64  |->_)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "sm" ) )) # Int64  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((Zlength (row_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
.

Definition solver_partial_solve_wit_22_aux := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval)) (PreH3 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH4 : (S = (n_pre + 1 ))) (PreH5 : (cells = (S * S ))) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 2000)) (PreH8 : (1 <= q_pre)) (PreH9 : (q_pre <= 1000000)) (PreH10 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH11 : ((Zlength (queries_data)) = q_pre)) (PreH12 : (MatrixValuesBounded matrix_data n_pre )) (PreH13 : (QueriesBounded queries_data n_pre )) (PreH14 : (RawQueriesEncode queries_data raw_queries )) (PreH15 : (0 <= i)) (PreH16 : (i < q_pre)) (PreH17 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH18 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH19 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH20 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH21 : (1 <= x1)) (PreH22 : (x1 <= x2)) (PreH23 : (x2 < S)) (PreH24 : (1 <= y1)) (PreH25 : (y1 <= y2)) (PreH26 : (y2 < S)) (PreH27 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH28 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH29 : (RectanglesBounded row_l S 4002000000000000 )) (PreH30 : (RectanglesBounded col_l S 4002000000000000 )) (PreH31 : (RectIntermediatesSafe sum_l S )) (PreH32 : (RectIntermediatesSafe row_l S )) (PreH33 : (RectIntermediatesSafe col_l S )) (PreH34 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH35 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (2 <= S) ” 
  &&  “ (S <= 2001) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ (0 <= 4002000000000000) ” 
  &&  “ (4002000000000000 <= 4002000000000000) ” 
  &&  “ ((Zlength (row_l)) = (S * S )) ” 
  &&  “ (RectanglesBounded row_l S 4002000000000000 ) ” 
  &&  “ (RectIntermediatesSafe row_l S ) ” 
  &&  “ ((Zlength (row_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= (4 * (Z.pow (10) (12)) )) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) ) ” 
  &&  “ (RectanglesBounded row_l S 4002000000000000 ) ” 
  &&  “ (RectanglesBounded col_l S 4002000000000000 ) ” 
  &&  “ (RectIntermediatesSafe sum_l S ) ” 
  &&  “ (RectIntermediatesSafe row_l S ) ” 
  &&  “ (RectIntermediatesSafe col_l S ) ” 
  &&  “ (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_22 := solver_partial_solve_wit_22_pure -> solver_partial_solve_wit_22_aux.

Definition solver_partial_solve_wit_23_pure := 
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (S = (n_pre + 1 ))) (PreH2 : (cells = (S * S ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 1000000)) (PreH7 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH8 : ((Zlength (queries_data)) = q_pre)) (PreH9 : (MatrixValuesBounded matrix_data n_pre )) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : (RawQueriesEncode queries_data raw_queries )) (PreH12 : (0 <= i)) (PreH13 : (i < q_pre)) (PreH14 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH15 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH16 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH17 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH18 : (1 <= x1)) (PreH19 : (x1 <= x2)) (PreH20 : (x2 < S)) (PreH21 : (1 <= y1)) (PreH22 : (y1 <= y2)) (PreH23 : (y2 < S)) (PreH24 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH25 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH26 : (RectanglesBounded row_l S 4002000000000000 )) (PreH27 : (RectanglesBounded col_l S 4002000000000000 )) (PreH28 : (RectIntermediatesSafe sum_l S )) (PreH29 : (RectIntermediatesSafe row_l S )) (PreH30 : (RectIntermediatesSafe col_l S )) (PreH31 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH32 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "sm" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (2 <= S) ” 
  &&  “ (S <= 2001) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ ((Zlength (sum_l)) = (S * S )) ” 
  &&  “ (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) ) ” 
  &&  “ (RectIntermediatesSafe sum_l S ) ” 
  &&  “ ((Zlength (sum_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((4 * (Z.pow (10) (12)) ) <= 4002000000000000) ” 
  &&  “ (0 <= (4 * (Z.pow (10) (12)) )) ”
) \/
(
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (cells <= UINT_MAX)) (PreH2 : (cells >= 0)) (PreH3 : (y2 <= INT_MAX)) (PreH4 : (x2 <= INT_MAX)) (PreH5 : (y1 <= INT_MAX)) (PreH6 : (x1 <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (S <= INT_MAX)) (PreH9 : (q_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (y2 >= INT_MIN)) (PreH12 : (x2 >= INT_MIN)) (PreH13 : (y1 >= INT_MIN)) (PreH14 : (x1 >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (S >= INT_MIN)) (PreH17 : (q_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (S = (n_pre + 1 ))) (PreH20 : (cells = (S * S ))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : (1 <= q_pre)) (PreH24 : (q_pre <= 1000000)) (PreH25 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH26 : ((Zlength (queries_data)) = q_pre)) (PreH27 : (MatrixValuesBounded matrix_data n_pre )) (PreH28 : (QueriesBounded queries_data n_pre )) (PreH29 : (RawQueriesEncode queries_data raw_queries )) (PreH30 : (0 <= i)) (PreH31 : (i < q_pre)) (PreH32 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH33 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH34 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH35 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH36 : (1 <= x1)) (PreH37 : (x1 <= x2)) (PreH38 : (x2 < S)) (PreH39 : (1 <= y1)) (PreH40 : (y1 <= y2)) (PreH41 : (y2 < S)) (PreH42 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH43 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH44 : (RectanglesBounded row_l S 4002000000000000 )) (PreH45 : (RectanglesBounded col_l S 4002000000000000 )) (PreH46 : (RectIntermediatesSafe sum_l S )) (PreH47 : (RectIntermediatesSafe row_l S )) (PreH48 : (RectIntermediatesSafe col_l S )) (PreH49 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH50 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "sm" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= (4 * (Z.pow (10) (12)) )) ” 
  &&  “ ((4 * (Z.pow (10) (12)) ) <= 4002000000000000) ” 
  &&  “ ((Zlength (sum_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((Zlength (sum_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
).

Definition solver_partial_solve_wit_23_pure_split_goal_1 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (cells <= UINT_MAX)) (PreH2 : (cells >= 0)) (PreH3 : (y2 <= INT_MAX)) (PreH4 : (x2 <= INT_MAX)) (PreH5 : (y1 <= INT_MAX)) (PreH6 : (x1 <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (S <= INT_MAX)) (PreH9 : (q_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (y2 >= INT_MIN)) (PreH12 : (x2 >= INT_MIN)) (PreH13 : (y1 >= INT_MIN)) (PreH14 : (x1 >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (S >= INT_MIN)) (PreH17 : (q_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (S = (n_pre + 1 ))) (PreH20 : (cells = (S * S ))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : (1 <= q_pre)) (PreH24 : (q_pre <= 1000000)) (PreH25 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH26 : ((Zlength (queries_data)) = q_pre)) (PreH27 : (MatrixValuesBounded matrix_data n_pre )) (PreH28 : (QueriesBounded queries_data n_pre )) (PreH29 : (RawQueriesEncode queries_data raw_queries )) (PreH30 : (0 <= i)) (PreH31 : (i < q_pre)) (PreH32 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH33 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH34 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH35 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH36 : (1 <= x1)) (PreH37 : (x1 <= x2)) (PreH38 : (x2 < S)) (PreH39 : (1 <= y1)) (PreH40 : (y1 <= y2)) (PreH41 : (y2 < S)) (PreH42 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH43 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH44 : (RectanglesBounded row_l S 4002000000000000 )) (PreH45 : (RectanglesBounded col_l S 4002000000000000 )) (PreH46 : (RectIntermediatesSafe sum_l S )) (PreH47 : (RectIntermediatesSafe row_l S )) (PreH48 : (RectIntermediatesSafe col_l S )) (PreH49 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH50 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "sm" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (0 <= (4 * (Z.pow (10) (12)) )) ”
.

Definition solver_partial_solve_wit_23_pure_split_goal_2 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (cells <= UINT_MAX)) (PreH2 : (cells >= 0)) (PreH3 : (y2 <= INT_MAX)) (PreH4 : (x2 <= INT_MAX)) (PreH5 : (y1 <= INT_MAX)) (PreH6 : (x1 <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (S <= INT_MAX)) (PreH9 : (q_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (y2 >= INT_MIN)) (PreH12 : (x2 >= INT_MIN)) (PreH13 : (y1 >= INT_MIN)) (PreH14 : (x1 >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (S >= INT_MIN)) (PreH17 : (q_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (S = (n_pre + 1 ))) (PreH20 : (cells = (S * S ))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : (1 <= q_pre)) (PreH24 : (q_pre <= 1000000)) (PreH25 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH26 : ((Zlength (queries_data)) = q_pre)) (PreH27 : (MatrixValuesBounded matrix_data n_pre )) (PreH28 : (QueriesBounded queries_data n_pre )) (PreH29 : (RawQueriesEncode queries_data raw_queries )) (PreH30 : (0 <= i)) (PreH31 : (i < q_pre)) (PreH32 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH33 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH34 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH35 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH36 : (1 <= x1)) (PreH37 : (x1 <= x2)) (PreH38 : (x2 < S)) (PreH39 : (1 <= y1)) (PreH40 : (y1 <= y2)) (PreH41 : (y2 < S)) (PreH42 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH43 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH44 : (RectanglesBounded row_l S 4002000000000000 )) (PreH45 : (RectanglesBounded col_l S 4002000000000000 )) (PreH46 : (RectIntermediatesSafe sum_l S )) (PreH47 : (RectIntermediatesSafe row_l S )) (PreH48 : (RectIntermediatesSafe col_l S )) (PreH49 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH50 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "sm" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((4 * (Z.pow (10) (12)) ) <= 4002000000000000) ”
.

Definition solver_partial_solve_wit_23_pure_split_goal_3 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (cells <= UINT_MAX)) (PreH2 : (cells >= 0)) (PreH3 : (y2 <= INT_MAX)) (PreH4 : (x2 <= INT_MAX)) (PreH5 : (y1 <= INT_MAX)) (PreH6 : (x1 <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (S <= INT_MAX)) (PreH9 : (q_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (y2 >= INT_MIN)) (PreH12 : (x2 >= INT_MIN)) (PreH13 : (y1 >= INT_MIN)) (PreH14 : (x1 >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (S >= INT_MIN)) (PreH17 : (q_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (S = (n_pre + 1 ))) (PreH20 : (cells = (S * S ))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : (1 <= q_pre)) (PreH24 : (q_pre <= 1000000)) (PreH25 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH26 : ((Zlength (queries_data)) = q_pre)) (PreH27 : (MatrixValuesBounded matrix_data n_pre )) (PreH28 : (QueriesBounded queries_data n_pre )) (PreH29 : (RawQueriesEncode queries_data raw_queries )) (PreH30 : (0 <= i)) (PreH31 : (i < q_pre)) (PreH32 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH33 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH34 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH35 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH36 : (1 <= x1)) (PreH37 : (x1 <= x2)) (PreH38 : (x2 < S)) (PreH39 : (1 <= y1)) (PreH40 : (y1 <= y2)) (PreH41 : (y2 < S)) (PreH42 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH43 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH44 : (RectanglesBounded row_l S 4002000000000000 )) (PreH45 : (RectanglesBounded col_l S 4002000000000000 )) (PreH46 : (RectIntermediatesSafe sum_l S )) (PreH47 : (RectIntermediatesSafe row_l S )) (PreH48 : (RectIntermediatesSafe col_l S )) (PreH49 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH50 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "sm" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((Zlength (sum_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
.

Definition solver_partial_solve_wit_23_pure_split_goal_4 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (cells <= UINT_MAX)) (PreH2 : (cells >= 0)) (PreH3 : (y2 <= INT_MAX)) (PreH4 : (x2 <= INT_MAX)) (PreH5 : (y1 <= INT_MAX)) (PreH6 : (x1 <= INT_MAX)) (PreH7 : (i <= INT_MAX)) (PreH8 : (S <= INT_MAX)) (PreH9 : (q_pre <= INT_MAX)) (PreH10 : (n_pre <= INT_MAX)) (PreH11 : (y2 >= INT_MIN)) (PreH12 : (x2 >= INT_MIN)) (PreH13 : (y1 >= INT_MIN)) (PreH14 : (x1 >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (S >= INT_MIN)) (PreH17 : (q_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (S = (n_pre + 1 ))) (PreH20 : (cells = (S * S ))) (PreH21 : (1 <= n_pre)) (PreH22 : (n_pre <= 2000)) (PreH23 : (1 <= q_pre)) (PreH24 : (q_pre <= 1000000)) (PreH25 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH26 : ((Zlength (queries_data)) = q_pre)) (PreH27 : (MatrixValuesBounded matrix_data n_pre )) (PreH28 : (QueriesBounded queries_data n_pre )) (PreH29 : (RawQueriesEncode queries_data raw_queries )) (PreH30 : (0 <= i)) (PreH31 : (i < q_pre)) (PreH32 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH33 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH34 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH35 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH36 : (1 <= x1)) (PreH37 : (x1 <= x2)) (PreH38 : (x2 < S)) (PreH39 : (1 <= y1)) (PreH40 : (y1 <= y2)) (PreH41 : (y2 < S)) (PreH42 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH43 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH44 : (RectanglesBounded row_l S 4002000000000000 )) (PreH45 : (RectanglesBounded col_l S 4002000000000000 )) (PreH46 : (RectIntermediatesSafe sum_l S )) (PreH47 : (RectIntermediatesSafe row_l S )) (PreH48 : (RectIntermediatesSafe col_l S )) (PreH49 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH50 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  ((( &( "sm" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "matrix" ) )) # Ptr  |-> matrix_pre)
  **  ((( &( "q" ) )) # Int  |-> q_pre)
  **  ((( &( "queries" ) )) # Ptr  |-> queries_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "S" ) )) # Int  |-> S)
  **  ((( &( "cells" ) )) # UInt  |-> cells)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "x1" ) )) # Int  |-> x1)
  **  ((( &( "y1" ) )) # Int  |-> y1)
  **  ((( &( "x2" ) )) # Int  |-> x2)
  **  ((( &( "y2" ) )) # Int  |-> y2)
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  ((( &( "sum" ) )) # Ptr  |-> sum)
  **  (Int64Array.full sum (S * S ) sum_l )
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  (Int64Array.full row (S * S ) row_l )
  **  ((( &( "col" ) )) # Ptr  |-> col)
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ ((Zlength (sum_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ”
.

Definition solver_partial_solve_wit_23_aux := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (S = (n_pre + 1 ))) (PreH2 : (cells = (S * S ))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 2000)) (PreH5 : (1 <= q_pre)) (PreH6 : (q_pre <= 1000000)) (PreH7 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH8 : ((Zlength (queries_data)) = q_pre)) (PreH9 : (MatrixValuesBounded matrix_data n_pre )) (PreH10 : (QueriesBounded queries_data n_pre )) (PreH11 : (RawQueriesEncode queries_data raw_queries )) (PreH12 : (0 <= i)) (PreH13 : (i < q_pre)) (PreH14 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH15 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH16 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH17 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH18 : (1 <= x1)) (PreH19 : (x1 <= x2)) (PreH20 : (x2 < S)) (PreH21 : (1 <= y1)) (PreH22 : (y1 <= y2)) (PreH23 : (y2 < S)) (PreH24 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH25 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH26 : (RectanglesBounded row_l S 4002000000000000 )) (PreH27 : (RectanglesBounded col_l S 4002000000000000 )) (PreH28 : (RectIntermediatesSafe sum_l S )) (PreH29 : (RectIntermediatesSafe row_l S )) (PreH30 : (RectIntermediatesSafe col_l S )) (PreH31 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH32 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (2 <= S) ” 
  &&  “ (S <= 2001) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ ((Zlength (sum_l)) = (S * S )) ” 
  &&  “ (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) ) ” 
  &&  “ (RectIntermediatesSafe sum_l S ) ” 
  &&  “ ((Zlength (sum_l)) = ((n_pre + 1 ) * (n_pre + 1 ) )) ” 
  &&  “ ((4 * (Z.pow (10) (12)) ) <= 4002000000000000) ” 
  &&  “ (0 <= (4 * (Z.pow (10) (12)) )) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) ) ” 
  &&  “ (RectanglesBounded row_l S 4002000000000000 ) ” 
  &&  “ (RectanglesBounded col_l S 4002000000000000 ) ” 
  &&  “ (RectIntermediatesSafe sum_l S ) ” 
  &&  “ (RectIntermediatesSafe row_l S ) ” 
  &&  “ (RectIntermediatesSafe col_l S ) ” 
  &&  “ (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_23 := solver_partial_solve_wit_23_pure -> solver_partial_solve_wit_23_aux.

Definition solver_partial_solve_wit_24 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (result: (@list Z)) (S: Z) (cells: Z) (i: Z) (x1: Z) (y1: Z) (x2: Z) (y2: Z) (sum: Z) (row: Z) (col: Z) (retval: Z) (retval_2: Z) (retval_3: Z)  __default__Prod__Prod__Prod_Z_Z_Z_Z (PreH1 : (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2)))) (PreH2 : (0 <= retval_3)) (PreH3 : (retval_3 <= 4002000000000000)) (PreH4 : (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2)))) (PreH5 : (0 <= retval_2)) (PreH6 : (retval_2 <= 4002000000000000)) (PreH7 : (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2)))) (PreH8 : (0 <= retval)) (PreH9 : (retval <= (4 * (Z.pow (10) (12)) ))) (PreH10 : (S = (n_pre + 1 ))) (PreH11 : (cells = (S * S ))) (PreH12 : (1 <= n_pre)) (PreH13 : (n_pre <= 2000)) (PreH14 : (1 <= q_pre)) (PreH15 : (q_pre <= 1000000)) (PreH16 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH17 : ((Zlength (queries_data)) = q_pre)) (PreH18 : (MatrixValuesBounded matrix_data n_pre )) (PreH19 : (QueriesBounded queries_data n_pre )) (PreH20 : (RawQueriesEncode queries_data raw_queries )) (PreH21 : (0 <= i)) (PreH22 : (i < q_pre)) (PreH23 : (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH24 : (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH25 : (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH26 : (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 ))) (PreH27 : (1 <= x1)) (PreH28 : (x1 <= x2)) (PreH29 : (x2 < S)) (PreH30 : (1 <= y1)) (PreH31 : (y1 <= y2)) (PreH32 : (y2 < S)) (PreH33 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH34 : (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) )) (PreH35 : (RectanglesBounded row_l S 4002000000000000 )) (PreH36 : (RectanglesBounded col_l S 4002000000000000 )) (PreH37 : (RectIntermediatesSafe sum_l S )) (PreH38 : (RectIntermediatesSafe row_l S )) (PreH39 : (RectIntermediatesSafe col_l S )) (PreH40 : (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 )) (PreH41 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
|--
  “ (retval_3 = (RectLookup (col_l) (S) (x1) (y1) (x2) (y2))) ” 
  &&  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= 4002000000000000) ” 
  &&  “ (retval_2 = (RectLookup (row_l) (S) (x1) (y1) (x2) (y2))) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= 4002000000000000) ” 
  &&  “ (retval = (RectLookup (sum_l) (S) (x1) (y1) (x2) (y2))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= (4 * (Z.pow (10) (12)) )) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < q_pre) ” 
  &&  “ (x1 = ((zquad_1 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (y1 = ((zquad_2 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (x2 = ((zquad_3 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (y2 = ((zquad_4 ((Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z))) + 1 )) ” 
  &&  “ (1 <= x1) ” 
  &&  “ (x1 <= x2) ” 
  &&  “ (x2 < S) ” 
  &&  “ (1 <= y1) ” 
  &&  “ (y1 <= y2) ” 
  &&  “ (y2 < S) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (RectanglesBounded sum_l S (4 * (Z.pow (10) (12)) ) ) ” 
  &&  “ (RectanglesBounded row_l S 4002000000000000 ) ” 
  &&  “ (RectanglesBounded col_l S 4002000000000000 ) ” 
  &&  “ (RectIntermediatesSafe sum_l S ) ” 
  &&  “ (RectIntermediatesSafe row_l S ) ” 
  &&  “ (RectIntermediatesSafe col_l S ) ” 
  &&  “ (QueryArithmeticSafe sum_l row_l col_l S x1 y1 x2 y2 ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (((out_pre + (i * sizeof(INT64)))) # Int64  |->_)
  **  (Int64Array.undef_seg out_pre (i + 1 ) q_pre )
  **  (Int64Array.full col (S * S ) col_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
.

Definition solver_partial_solve_wit_25 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (sum: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i >= q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.undef_seg out_pre i q_pre )
  **  (Int64Array.full sum (S * S ) sum_l )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (i >= q_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (Int64Array.full sum ((n_pre + 1 ) * (n_pre + 1 ) ) sum_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_26 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (row: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i >= q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.full row (S * S ) row_l )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (i >= q_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (Int64Array.full row ((n_pre + 1 ) * (n_pre + 1 ) ) row_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.full col (S * S ) col_l )
.

Definition solver_partial_solve_wit_27 := 
forall (out_pre: Z) (queries_pre: Z) (q_pre: Z) (matrix_pre: Z) (n_pre: Z) (raw_queries: (@list Z)) (queries_data: (@list (((Z * Z) * Z) * Z))) (matrix_data: (@list Z)) (col: Z) (result: (@list Z)) (sum_l: (@list Z)) (row_l: (@list Z)) (col_l: (@list Z)) (i: Z) (cells: Z) (S: Z) (PreH1 : (i >= q_pre)) (PreH2 : (S = (n_pre + 1 ))) (PreH3 : (cells = (S * S ))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 2000)) (PreH6 : (1 <= q_pre)) (PreH7 : (q_pre <= 1000000)) (PreH8 : ((Zlength (matrix_data)) = (n_pre * n_pre ))) (PreH9 : ((Zlength (queries_data)) = q_pre)) (PreH10 : (MatrixValuesBounded matrix_data n_pre )) (PreH11 : (QueriesBounded queries_data n_pre )) (PreH12 : (RawQueriesEncode queries_data raw_queries )) (PreH13 : (0 <= i)) (PreH14 : (i <= q_pre)) (PreH15 : (TablesReady matrix_data sum_l row_l col_l n_pre S )) (PreH16 : (OutputPrefix matrix_data n_pre queries_data result i )) ,
  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
  **  (Int64Array.full col (S * S ) col_l )
|--
  “ (i >= q_pre) ” 
  &&  “ (S = (n_pre + 1 )) ” 
  &&  “ (cells = (S * S )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 2000) ” 
  &&  “ (1 <= q_pre) ” 
  &&  “ (q_pre <= 1000000) ” 
  &&  “ ((Zlength (matrix_data)) = (n_pre * n_pre )) ” 
  &&  “ ((Zlength (queries_data)) = q_pre) ” 
  &&  “ (MatrixValuesBounded matrix_data n_pre ) ” 
  &&  “ (QueriesBounded queries_data n_pre ) ” 
  &&  “ (RawQueriesEncode queries_data raw_queries ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= q_pre) ” 
  &&  “ (TablesReady matrix_data sum_l row_l col_l n_pre S ) ” 
  &&  “ (OutputPrefix matrix_data n_pre queries_data result i ) ”
  &&  (Int64Array.full col ((n_pre + 1 ) * (n_pre + 1 ) ) col_l )
  **  (Int64Array.full matrix_pre (n_pre * n_pre ) matrix_data )
  **  (IntArray.full queries_pre (4 * q_pre ) raw_queries )
  **  (Int64Array.seg out_pre 0 i result )
.

Module Type VC_Correct.


Axiom proof_of_rect_safety_wit_1 : rect_safety_wit_1.
Axiom proof_of_rect_safety_wit_2 : rect_safety_wit_2.
Axiom proof_of_rect_safety_wit_3 : rect_safety_wit_3.
Axiom proof_of_rect_safety_wit_4 : rect_safety_wit_4.
Axiom proof_of_rect_safety_wit_5 : rect_safety_wit_5.
Axiom proof_of_rect_safety_wit_6 : rect_safety_wit_6.
Axiom proof_of_rect_safety_wit_7 : rect_safety_wit_7.
Axiom proof_of_rect_safety_wit_8 : rect_safety_wit_8.
Axiom proof_of_rect_safety_wit_9 : rect_safety_wit_9.
Axiom proof_of_rect_safety_wit_10 : rect_safety_wit_10.
Axiom proof_of_rect_safety_wit_11 : rect_safety_wit_11.
Axiom proof_of_rect_safety_wit_12 : rect_safety_wit_12.
Axiom proof_of_rect_safety_wit_13 : rect_safety_wit_13.
Axiom proof_of_rect_safety_wit_14 : rect_safety_wit_14.
Axiom proof_of_rect_safety_wit_15 : rect_safety_wit_15.
Axiom proof_of_rect_safety_wit_16 : rect_safety_wit_16.
Axiom proof_of_rect_safety_wit_17 : rect_safety_wit_17.
Axiom proof_of_rect_safety_wit_18 : rect_safety_wit_18.
Axiom proof_of_rect_safety_wit_19 : rect_safety_wit_19.
Axiom proof_of_rect_entail_wit_1 : rect_entail_wit_1.
Axiom proof_of_rect_return_wit_1 : rect_return_wit_1.
Axiom proof_of_rect_partial_solve_wit_1 : rect_partial_solve_wit_1.
Axiom proof_of_rect_partial_solve_wit_2 : rect_partial_solve_wit_2.
Axiom proof_of_rect_partial_solve_wit_3 : rect_partial_solve_wit_3.
Axiom proof_of_rect_partial_solve_wit_4 : rect_partial_solve_wit_4.
Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_safety_wit_45 : solver_safety_wit_45.
Axiom proof_of_solver_safety_wit_46 : solver_safety_wit_46.
Axiom proof_of_solver_safety_wit_47 : solver_safety_wit_47.
Axiom proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Axiom proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Axiom proof_of_solver_safety_wit_50 : solver_safety_wit_50.
Axiom proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Axiom proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Axiom proof_of_solver_safety_wit_53 : solver_safety_wit_53.
Axiom proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Axiom proof_of_solver_safety_wit_55 : solver_safety_wit_55.
Axiom proof_of_solver_safety_wit_56 : solver_safety_wit_56.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21_pure : solver_partial_solve_wit_21_pure.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22_pure : solver_partial_solve_wit_22_pure.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23_pure : solver_partial_solve_wit_23_pure.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.

End VC_Correct.
