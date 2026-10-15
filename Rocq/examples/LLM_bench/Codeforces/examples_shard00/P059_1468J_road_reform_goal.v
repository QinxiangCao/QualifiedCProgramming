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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P059_1468J_road_reform_lib.
Local Open Scope sac.

(*----- Function cmp_edge -----*)

Definition cmp_edge_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH2 : ((ztriple_3 (left)) > (ztriple_3 (right)))) ,
  ((( &( "b" ) )) # Int64  |-> (ztriple_3 (right)))
  **  ((( &( "a" ) )) # Int64  |-> (ztriple_3 (left)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ ((1 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 - 0 )) ”
.

Definition cmp_edge_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (left)) < (ztriple_3 (right)))) (PreH2 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((( &( "b" ) )) # Int64  |-> (ztriple_3 (right)))
  **  ((( &( "a" ) )) # Int64  |-> (ztriple_3 (left)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ ((0 - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 1 )) ”
.

Definition cmp_edge_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH2 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((( &( "b" ) )) # Int64  |-> (ztriple_3 (right)))
  **  ((( &( "a" ) )) # Int64  |-> (ztriple_3 (left)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ ((0 - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 - 0 )) ”
.

Definition cmp_edge_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (left)) < (ztriple_3 (right)))) (PreH2 : ((ztriple_3 (left)) > (ztriple_3 (right)))) ,
  ((( &( "b" ) )) # Int64  |-> (ztriple_3 (right)))
  **  ((( &( "a" ) )) # Int64  |-> (ztriple_3 (left)))
  **  ((( &( "x" ) )) # Ptr  |-> x_pre)
  **  ((( &( "y" ) )) # Ptr  |-> y_pre)
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ False ”
.

Definition cmp_edge_entail_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) ,
  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
|--
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
) \/
(
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) ,
  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
|--
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
).

Definition cmp_edge_entail_wit_1_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) ,
  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
|--
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
.

Definition cmp_edge_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH2 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ (RoadCompareResult left right (0 - 0 ) ) ”
  &&  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (right)) <= INT64_MAX)) (PreH2 : ((ztriple_3 (left)) <= INT64_MAX)) (PreH3 : ((ztriple_3 (right)) >= INT64_MIN)) (PreH4 : ((ztriple_3 (left)) >= INT64_MIN)) (PreH5 : (((ztriple_2 (right)) - 1 ) <= INT_MAX)) (PreH6 : (((ztriple_1 (right)) - 1 ) <= INT_MAX)) (PreH7 : (((ztriple_2 (left)) - 1 ) <= INT_MAX)) (PreH8 : (((ztriple_1 (left)) - 1 ) <= INT_MAX)) (PreH9 : (((ztriple_2 (right)) - 1 ) >= INT_MIN)) (PreH10 : (((ztriple_1 (right)) - 1 ) >= INT_MIN)) (PreH11 : (((ztriple_2 (left)) - 1 ) >= INT_MIN)) (PreH12 : (((ztriple_1 (left)) - 1 ) >= INT_MIN)) (PreH13 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH14 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ (RoadCompareResult left right (0 - 0 ) ) ”
  &&  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
).

Definition cmp_edge_return_wit_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (right)) <= INT64_MAX)) (PreH2 : ((ztriple_3 (left)) <= INT64_MAX)) (PreH3 : ((ztriple_3 (right)) >= INT64_MIN)) (PreH4 : ((ztriple_3 (left)) >= INT64_MIN)) (PreH5 : (((ztriple_2 (right)) - 1 ) <= INT_MAX)) (PreH6 : (((ztriple_1 (right)) - 1 ) <= INT_MAX)) (PreH7 : (((ztriple_2 (left)) - 1 ) <= INT_MAX)) (PreH8 : (((ztriple_1 (left)) - 1 ) <= INT_MAX)) (PreH9 : (((ztriple_2 (right)) - 1 ) >= INT_MIN)) (PreH10 : (((ztriple_1 (right)) - 1 ) >= INT_MIN)) (PreH11 : (((ztriple_2 (left)) - 1 ) >= INT_MIN)) (PreH12 : (((ztriple_1 (left)) - 1 ) >= INT_MIN)) (PreH13 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH14 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ (RoadCompareResult left right (0 - 0 ) ) ”
.

Definition cmp_edge_return_wit_1_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (right)) <= INT64_MAX)) (PreH2 : ((ztriple_3 (left)) <= INT64_MAX)) (PreH3 : ((ztriple_3 (right)) >= INT64_MIN)) (PreH4 : ((ztriple_3 (left)) >= INT64_MIN)) (PreH5 : (((ztriple_2 (right)) - 1 ) <= INT_MAX)) (PreH6 : (((ztriple_1 (right)) - 1 ) <= INT_MAX)) (PreH7 : (((ztriple_2 (left)) - 1 ) <= INT_MAX)) (PreH8 : (((ztriple_1 (left)) - 1 ) <= INT_MAX)) (PreH9 : (((ztriple_2 (right)) - 1 ) >= INT_MIN)) (PreH10 : (((ztriple_1 (right)) - 1 ) >= INT_MIN)) (PreH11 : (((ztriple_2 (left)) - 1 ) >= INT_MIN)) (PreH12 : (((ztriple_1 (left)) - 1 ) >= INT_MIN)) (PreH13 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH14 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
.

Definition cmp_edge_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (left)) < (ztriple_3 (right)))) (PreH2 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ (RoadCompareResult left right (0 - 1 ) ) ”
  &&  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (right)) <= INT64_MAX)) (PreH2 : ((ztriple_3 (left)) <= INT64_MAX)) (PreH3 : ((ztriple_3 (right)) >= INT64_MIN)) (PreH4 : ((ztriple_3 (left)) >= INT64_MIN)) (PreH5 : (((ztriple_2 (right)) - 1 ) <= INT_MAX)) (PreH6 : (((ztriple_1 (right)) - 1 ) <= INT_MAX)) (PreH7 : (((ztriple_2 (left)) - 1 ) <= INT_MAX)) (PreH8 : (((ztriple_1 (left)) - 1 ) <= INT_MAX)) (PreH9 : (((ztriple_2 (right)) - 1 ) >= INT_MIN)) (PreH10 : (((ztriple_1 (right)) - 1 ) >= INT_MIN)) (PreH11 : (((ztriple_2 (left)) - 1 ) >= INT_MIN)) (PreH12 : (((ztriple_1 (left)) - 1 ) >= INT_MIN)) (PreH13 : ((ztriple_3 (left)) < (ztriple_3 (right)))) (PreH14 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ (RoadCompareResult left right (0 - 1 ) ) ”
  &&  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
).

Definition cmp_edge_return_wit_2_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (right)) <= INT64_MAX)) (PreH2 : ((ztriple_3 (left)) <= INT64_MAX)) (PreH3 : ((ztriple_3 (right)) >= INT64_MIN)) (PreH4 : ((ztriple_3 (left)) >= INT64_MIN)) (PreH5 : (((ztriple_2 (right)) - 1 ) <= INT_MAX)) (PreH6 : (((ztriple_1 (right)) - 1 ) <= INT_MAX)) (PreH7 : (((ztriple_2 (left)) - 1 ) <= INT_MAX)) (PreH8 : (((ztriple_1 (left)) - 1 ) <= INT_MAX)) (PreH9 : (((ztriple_2 (right)) - 1 ) >= INT_MIN)) (PreH10 : (((ztriple_1 (right)) - 1 ) >= INT_MIN)) (PreH11 : (((ztriple_2 (left)) - 1 ) >= INT_MIN)) (PreH12 : (((ztriple_1 (left)) - 1 ) >= INT_MIN)) (PreH13 : ((ztriple_3 (left)) < (ztriple_3 (right)))) (PreH14 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ (RoadCompareResult left right (0 - 1 ) ) ”
.

Definition cmp_edge_return_wit_2_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (right)) <= INT64_MAX)) (PreH2 : ((ztriple_3 (left)) <= INT64_MAX)) (PreH3 : ((ztriple_3 (right)) >= INT64_MIN)) (PreH4 : ((ztriple_3 (left)) >= INT64_MIN)) (PreH5 : (((ztriple_2 (right)) - 1 ) <= INT_MAX)) (PreH6 : (((ztriple_1 (right)) - 1 ) <= INT_MAX)) (PreH7 : (((ztriple_2 (left)) - 1 ) <= INT_MAX)) (PreH8 : (((ztriple_1 (left)) - 1 ) <= INT_MAX)) (PreH9 : (((ztriple_2 (right)) - 1 ) >= INT_MIN)) (PreH10 : (((ztriple_1 (right)) - 1 ) >= INT_MIN)) (PreH11 : (((ztriple_2 (left)) - 1 ) >= INT_MIN)) (PreH12 : (((ztriple_1 (left)) - 1 ) >= INT_MIN)) (PreH13 : ((ztriple_3 (left)) < (ztriple_3 (right)))) (PreH14 : ((ztriple_3 (left)) <= (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
.

Definition cmp_edge_return_wit_3 := 
(
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH2 : ((ztriple_3 (left)) > (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ (RoadCompareResult left right (1 - 0 ) ) ”
  &&  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
) \/
(
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (right)) <= INT64_MAX)) (PreH2 : ((ztriple_3 (left)) <= INT64_MAX)) (PreH3 : ((ztriple_3 (right)) >= INT64_MIN)) (PreH4 : ((ztriple_3 (left)) >= INT64_MIN)) (PreH5 : (((ztriple_2 (right)) - 1 ) <= INT_MAX)) (PreH6 : (((ztriple_1 (right)) - 1 ) <= INT_MAX)) (PreH7 : (((ztriple_2 (left)) - 1 ) <= INT_MAX)) (PreH8 : (((ztriple_1 (left)) - 1 ) <= INT_MAX)) (PreH9 : (((ztriple_2 (right)) - 1 ) >= INT_MIN)) (PreH10 : (((ztriple_1 (right)) - 1 ) >= INT_MIN)) (PreH11 : (((ztriple_2 (left)) - 1 ) >= INT_MIN)) (PreH12 : (((ztriple_1 (left)) - 1 ) >= INT_MIN)) (PreH13 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH14 : ((ztriple_3 (left)) > (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ (RoadCompareResult left right (1 - 0 ) ) ”
  &&  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
).

Definition cmp_edge_return_wit_3_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (right)) <= INT64_MAX)) (PreH2 : ((ztriple_3 (left)) <= INT64_MAX)) (PreH3 : ((ztriple_3 (right)) >= INT64_MIN)) (PreH4 : ((ztriple_3 (left)) >= INT64_MIN)) (PreH5 : (((ztriple_2 (right)) - 1 ) <= INT_MAX)) (PreH6 : (((ztriple_1 (right)) - 1 ) <= INT_MAX)) (PreH7 : (((ztriple_2 (left)) - 1 ) <= INT_MAX)) (PreH8 : (((ztriple_1 (left)) - 1 ) <= INT_MAX)) (PreH9 : (((ztriple_2 (right)) - 1 ) >= INT_MIN)) (PreH10 : (((ztriple_1 (right)) - 1 ) >= INT_MIN)) (PreH11 : (((ztriple_2 (left)) - 1 ) >= INT_MIN)) (PreH12 : (((ztriple_1 (left)) - 1 ) >= INT_MIN)) (PreH13 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH14 : ((ztriple_3 (left)) > (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  “ (RoadCompareResult left right (1 - 0 ) ) ”
.

Definition cmp_edge_return_wit_3_split_goal_spatial := 
forall (y_pre: Z) (x_pre: Z) (right: ((Z * Z) * Z)) (left: ((Z * Z) * Z)) (PreH1 : ((ztriple_3 (right)) <= INT64_MAX)) (PreH2 : ((ztriple_3 (left)) <= INT64_MAX)) (PreH3 : ((ztriple_3 (right)) >= INT64_MIN)) (PreH4 : ((ztriple_3 (left)) >= INT64_MIN)) (PreH5 : (((ztriple_2 (right)) - 1 ) <= INT_MAX)) (PreH6 : (((ztriple_1 (right)) - 1 ) <= INT_MAX)) (PreH7 : (((ztriple_2 (left)) - 1 ) <= INT_MAX)) (PreH8 : (((ztriple_1 (left)) - 1 ) <= INT_MAX)) (PreH9 : (((ztriple_2 (right)) - 1 ) >= INT_MIN)) (PreH10 : (((ztriple_1 (right)) - 1 ) >= INT_MIN)) (PreH11 : (((ztriple_2 (left)) - 1 ) >= INT_MIN)) (PreH12 : (((ztriple_1 (left)) - 1 ) >= INT_MIN)) (PreH13 : ((ztriple_3 (left)) >= (ztriple_3 (right)))) (PreH14 : ((ztriple_3 (left)) > (ztriple_3 (right)))) ,
  ((&((x_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (left)) - 1 ))
  **  ((&((x_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (left)))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 (right)) - 1 ))
  **  ((&((y_pre)  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 (right)))
|--
  (EdgeArray.full x_pre 1 (cons (left) ((@nil ((Z * Z) * Z)))) )
  **  (EdgeArray.full y_pre 1 (cons (right) ((@nil ((Z * Z) * Z)))) )
.

(*----- Function find -----*)

Definition find_entail_wit_1 := 
(
forall (x_pre: Z) (p_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre < n)) (PreH3 : ((Zlength (parents)) = n)) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 parents 0)) /\ ((Znth i_2 parents 0) < n)))) (PreH5 : (DSUState n roads chosen parents )) ,
  (IntArray.full p_pre n parents )
|--
  EX (current_parents: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n) ” 
  &&  “ ((Zlength (current_parents)) = n) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n))) ” 
  &&  “ (DSUState n roads chosen parents ) ” 
  &&  “ (DSURootsPreserved parents current_parents ) ” 
  &&  “ (FindProgress n roads chosen x_pre x_pre current_parents ) ”
  &&  (IntArray.full p_pre n current_parents )
) \/
(
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre < n)) (PreH3 : ((Zlength (parents)) = n)) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 parents 0)) /\ ((Znth i_2 parents 0) < n)))) (PreH5 : (DSUState n roads chosen parents )) ,
  TT && emp 
|--
  “ (FindProgress n roads chosen x_pre x_pre parents ) ” 
  &&  “ (DSURootsPreserved parents parents ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i parents 0)) /\ ((Znth i parents 0) < n))) ”
  &&  emp
).

Definition find_entail_wit_1_split_goal_1 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre < n)) (PreH3 : ((Zlength (parents)) = n)) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 parents 0)) /\ ((Znth i_2 parents 0) < n)))) (PreH5 : (DSUState n roads chosen parents )) ,
  (FindProgress n roads chosen x_pre x_pre parents )
.

Definition find_entail_wit_1_split_goal_2 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre < n)) (PreH3 : ((Zlength (parents)) = n)) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 parents 0)) /\ ((Znth i_2 parents 0) < n)))) (PreH5 : (DSUState n roads chosen parents )) ,
  (DSURootsPreserved parents parents )
.

Definition find_entail_wit_1_split_goal_3 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre < n)) (PreH3 : ((Zlength (parents)) = n)) (PreH4 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 parents 0)) /\ ((Znth i_2 parents 0) < n)))) (PreH5 : (DSUState n roads chosen parents )) ,
  forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i parents 0)) /\ ((Znth i parents 0) < n)))
.

Definition find_entail_wit_2 := 
(
forall (x_pre: Z) (p_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents_2: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents_2 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents_2)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents_2 0)) /\ ((Znth i current_parents_2 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents_2 )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents_2 )) ,
  (IntArray.full p_pre n (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) )
|--
  EX (current_parents: (@list Z)) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n) ” 
  &&  “ (0 <= (Znth x (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) 0)) ” 
  &&  “ ((Znth x (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) 0) < n) ” 
  &&  “ ((Zlength (current_parents)) = n) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n))) ” 
  &&  “ (DSUState n roads chosen parents ) ” 
  &&  “ (DSURootsPreserved parents current_parents ) ” 
  &&  “ (FindProgress n roads chosen x_pre (Znth x (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) 0) current_parents ) ”
  &&  (IntArray.full p_pre n current_parents )
) \/
(
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents_2: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents_2 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents_2)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents_2 0)) /\ ((Znth i current_parents_2 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents_2 )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents_2 )) ,
  TT && emp 
|--
  “ (FindProgress n roads chosen x_pre (Znth x (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) 0) (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) ) ” 
  &&  “ (DSURootsPreserved parents (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) ) ” 
  &&  “ ((Zlength ((replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)))) = n) ” 
  &&  “ ((Znth x (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) 0) < n) ” 
  &&  “ (0 <= (Znth x (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) 0)) ”
  &&  emp
).

Definition find_entail_wit_2_split_goal_1 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents_2: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents_2 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents_2)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents_2 0)) /\ ((Znth i current_parents_2 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents_2 )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents_2 )) ,
  (FindProgress n roads chosen x_pre (Znth x (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) 0) (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) )
.

Definition find_entail_wit_2_split_goal_2 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents_2: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents_2 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents_2)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents_2 0)) /\ ((Znth i current_parents_2 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents_2 )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents_2 )) ,
  (DSURootsPreserved parents (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) )
.

Definition find_entail_wit_2_split_goal_3 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents_2: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents_2 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents_2)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents_2 0)) /\ ((Znth i current_parents_2 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents_2 )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents_2 )) ,
  ((Zlength ((replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)))) = n)
.

Definition find_entail_wit_2_split_goal_4 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents_2: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents_2 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents_2)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents_2 0)) /\ ((Znth i current_parents_2 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents_2 )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents_2 )) ,
  ((Znth x (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) 0) < n)
.

Definition find_entail_wit_2_split_goal_5 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents_2: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents_2 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents_2)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents_2 0)) /\ ((Znth i current_parents_2 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents_2 )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents_2 )) ,
  (0 <= (Znth x (replace_Znth (x) ((Znth (Znth x current_parents_2 0) current_parents_2 0)) (current_parents_2)) 0))
.

Definition find_return_wit_1 := 
(
forall (x_pre: Z) (p_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents 0) = x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents)) = n)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 current_parents 0)) /\ ((Znth i_2 current_parents 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents )) ,
  (IntArray.full p_pre n current_parents )
|--
  EX (parents_after: (@list Z)) ,
  “ (0 <= x) ” 
  &&  “ (x < n) ” 
  &&  “ ((Zlength (parents_after)) = n) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i parents_after 0)) /\ ((Znth i parents_after 0) < n))) ” 
  &&  “ (DSURootsPreserved parents parents_after ) ” 
  &&  “ (DSUFindResult n roads chosen parents parents_after x_pre x ) ”
  &&  (IntArray.full p_pre n parents_after )
) \/
(
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents 0) = x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents)) = n)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 current_parents 0)) /\ ((Znth i_2 current_parents 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents )) ,
  TT && emp 
|--
  “ (DSUFindResult n roads chosen parents current_parents x_pre x ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n))) ”
  &&  emp
).

Definition find_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents 0) = x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents)) = n)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 current_parents 0)) /\ ((Znth i_2 current_parents 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents )) ,
  (DSUFindResult n roads chosen parents current_parents x_pre x )
.

Definition find_return_wit_1_split_goal_2 := 
forall (x_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents 0) = x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents)) = n)) (PreH7 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n)) -> ((0 <= (Znth i_2 current_parents 0)) /\ ((Znth i_2 current_parents 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents )) ,
  forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n)))
.

Definition find_partial_solve_wit_1 := 
forall (x_pre: Z) (p_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents: (@list Z)) (x: Z) (PreH1 : (0 <= x_pre)) (PreH2 : (x_pre < n)) (PreH3 : (0 <= x)) (PreH4 : (x < n)) (PreH5 : ((Zlength (current_parents)) = n)) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n)))) (PreH7 : (DSUState n roads chosen parents )) (PreH8 : (DSURootsPreserved parents current_parents )) (PreH9 : (FindProgress n roads chosen x_pre x current_parents )) ,
  (IntArray.full p_pre n current_parents )
|--
  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n) ” 
  &&  “ ((Zlength (current_parents)) = n) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n))) ” 
  &&  “ (DSUState n roads chosen parents ) ” 
  &&  “ (DSURootsPreserved parents current_parents ) ” 
  &&  “ (FindProgress n roads chosen x_pre x current_parents ) ”
  &&  (((p_pre + (x * sizeof(INT)))) # Int  |-> (Znth x current_parents 0))
  **  (IntArray.missing_i p_pre x 0 n current_parents )
.

Definition find_partial_solve_wit_2 := 
forall (x_pre: Z) (p_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents )) ,
  (IntArray.full p_pre n current_parents )
|--
  “ ((Znth x current_parents 0) <> x) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n) ” 
  &&  “ ((Zlength (current_parents)) = n) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n))) ” 
  &&  “ (DSUState n roads chosen parents ) ” 
  &&  “ (DSURootsPreserved parents current_parents ) ” 
  &&  “ (FindProgress n roads chosen x_pre x current_parents ) ”
  &&  (((p_pre + (x * sizeof(INT)))) # Int  |-> (Znth x current_parents 0))
  **  (IntArray.missing_i p_pre x 0 n current_parents )
.

Definition find_partial_solve_wit_3 := 
forall (x_pre: Z) (p_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents )) ,
  (IntArray.full p_pre n current_parents )
|--
  “ ((Znth x current_parents 0) <> x) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n) ” 
  &&  “ ((Zlength (current_parents)) = n) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n))) ” 
  &&  “ (DSUState n roads chosen parents ) ” 
  &&  “ (DSURootsPreserved parents current_parents ) ” 
  &&  “ (FindProgress n roads chosen x_pre x current_parents ) ”
  &&  (((p_pre + ((Znth x current_parents 0) * sizeof(INT)))) # Int  |-> (Znth (Znth x current_parents 0) current_parents 0))
  **  (IntArray.missing_i p_pre (Znth x current_parents 0) 0 n current_parents )
.

Definition find_partial_solve_wit_4 := 
forall (x_pre: Z) (p_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents )) ,
  (IntArray.full p_pre n current_parents )
|--
  “ ((Znth x current_parents 0) <> x) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n) ” 
  &&  “ ((Zlength (current_parents)) = n) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n))) ” 
  &&  “ (DSUState n roads chosen parents ) ” 
  &&  “ (DSURootsPreserved parents current_parents ) ” 
  &&  “ (FindProgress n roads chosen x_pre x current_parents ) ”
  &&  (((p_pre + (x * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i p_pre x 0 n current_parents )
.

Definition find_partial_solve_wit_5 := 
forall (x_pre: Z) (p_pre: Z) (parents: (@list Z)) (chosen: (@list Z)) (roads: (@list ((Z * Z) * Z))) (n: Z) (current_parents: (@list Z)) (x: Z) (PreH1 : ((Znth x current_parents 0) <> x)) (PreH2 : (0 <= x_pre)) (PreH3 : (x_pre < n)) (PreH4 : (0 <= x)) (PreH5 : (x < n)) (PreH6 : ((Zlength (current_parents)) = n)) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n)))) (PreH8 : (DSUState n roads chosen parents )) (PreH9 : (DSURootsPreserved parents current_parents )) (PreH10 : (FindProgress n roads chosen x_pre x current_parents )) ,
  (IntArray.full p_pre n (replace_Znth (x) ((Znth (Znth x current_parents 0) current_parents 0)) (current_parents)) )
|--
  “ ((Znth x current_parents 0) <> x) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < n) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < n) ” 
  &&  “ ((Zlength (current_parents)) = n) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n)) -> ((0 <= (Znth i current_parents 0)) /\ ((Znth i current_parents 0) < n))) ” 
  &&  “ (DSUState n roads chosen parents ) ” 
  &&  “ (DSURootsPreserved parents current_parents ) ” 
  &&  “ (FindProgress n roads chosen x_pre x current_parents ) ”
  &&  (((p_pre + (x * sizeof(INT)))) # Int  |-> (Znth x (replace_Znth (x) ((Znth (Znth x current_parents 0) current_parents 0)) (current_parents)) 0))
  **  (IntArray.missing_i p_pre x 0 n (replace_Znth (x) ((Znth (Znth x current_parents 0) current_parents 0)) (current_parents)) )
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (EdgeAllocationFits m_pre )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH9 : (Pre n_pre k_pre roads )) (PreH10 : (m_pre = (Zlength (roads)))) ,
  ((( &( "closest" ) )) # Int64  |->_)
  **  (EdgeArray.undef_full retval m_pre )
  **  ((( &( "e" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ ((signed_last_nbits ((1 * (2^62) )) (64)) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (signed_last_nbits ((1 * (2^62) )) (64))) ” 
  &&  “ (62 <= 63) ” 
  &&  “ (0 <= 62) ”
.

Definition solver_safety_wit_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (EdgeAllocationFits m_pre )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH9 : (Pre n_pre k_pre roads )) (PreH10 : (m_pre = (Zlength (roads)))) ,
  ((( &( "closest" ) )) # Int64  |->_)
  **  (EdgeArray.undef_full retval m_pre )
  **  ((( &( "e" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (1 <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (EdgeAllocationFits m_pre )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH9 : (Pre n_pre k_pre roads )) (PreH10 : (m_pre = (Zlength (roads)))) ,
  ((( &( "closest" ) )) # Int64  |->_)
  **  (EdgeArray.undef_full retval m_pre )
  **  ((( &( "e" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (62 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 62) ”
.

Definition solver_safety_wit_4 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (EdgeAllocationFits m_pre )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH9 : (Pre n_pre k_pre roads )) (PreH10 : (m_pre = (Zlength (roads)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "closest" ) )) # Int64  |-> (Z.shiftl 1 62))
  **  (EdgeArray.undef_full retval m_pre )
  **  ((( &( "e" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_5 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= i)) (PreH5 : (i < m_pre)) (PreH6 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre )) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= i)) (PreH5 : (i < m_pre)) (PreH6 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre )) ”
).

Definition solver_safety_wit_5_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= i)) (PreH5 : (i < m_pre)) (PreH6 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) <= INT64_MAX) ”
.

Definition solver_safety_wit_5_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= i)) (PreH5 : (i < m_pre)) (PreH6 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((INT64_MIN) <= ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre )) ”
.

Definition solver_safety_wit_6 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= i)) (PreH5 : (i < m_pre)) (PreH6 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) )) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= i)) (PreH5 : (i < m_pre)) (PreH6 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) )) ”
).

Definition solver_safety_wit_6_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= i)) (PreH5 : (i < m_pre)) (PreH6 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_6_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= i)) (PreH5 : (i < m_pre)) (PreH6 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "d" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((INT64_MIN) <= (k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) )) ”
.

Definition solver_safety_wit_7 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH3 : (m_pre = (Zlength (roads)))) (PreH4 : (Pre n_pre k_pre roads )) (PreH5 : (0 <= i)) (PreH6 : (i < m_pre)) (PreH7 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ))
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_8 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH3 : (m_pre = (Zlength (roads)))) (PreH4 : (Pre n_pre k_pre roads )) (PreH5 : (0 <= i)) (PreH6 : (i < m_pre)) (PreH7 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> (k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ))
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH3 : (m_pre = (Zlength (roads)))) (PreH4 : (Pre n_pre k_pre roads )) (PreH5 : (0 <= i)) (PreH6 : (i < m_pre)) (PreH7 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH3 : (m_pre = (Zlength (roads)))) (PreH4 : (Pre n_pre k_pre roads )) (PreH5 : (0 <= i)) (PreH6 : (i < m_pre)) (PreH7 : (ClosestRoadPrefix k_pre roads i closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (e: Z) (sorted: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (RoadSortResult roads sorted sorted_raw order )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= closest)) (PreH11 : (closest <= 1000000000)) (PreH12 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval n_pre )
  **  ((( &( "p" ) )) # Ptr  |-> retval)
  **  (EdgeArray.full e m_pre sorted )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_12 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (initialized_parents: (@list Z)) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (closest: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= closest)) (PreH12 : (closest <= 1000000000)) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH15 : ((Zlength (initialized_parents)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j initialized_parents 0) = j))) ,
  (IntArray.full p (i + 1 ) (app (initialized_parents) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg p (i + 1 ) n_pre )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_13 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (initialized_parents: (@list Z)) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (0 <= closest)) (PreH8 : (closest <= 1000000000)) (PreH9 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH10 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH11 : ((Zlength (initialized_parents)) = n_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((((Znth j initialized_parents 0) = j) /\ (0 <= (Znth j initialized_parents 0))) /\ ((Znth j initialized_parents 0) < n_pre)))) (PreH13 : (DSUState n_pre roads (@nil Z) initialized_parents )) ,
  ((( &( "sum" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre initialized_parents )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_14 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (initialized_parents: (@list Z)) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (0 <= closest)) (PreH8 : (closest <= 1000000000)) (PreH9 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH10 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH11 : ((Zlength (initialized_parents)) = n_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((((Znth j initialized_parents 0) = j) /\ (0 <= (Znth j initialized_parents 0))) /\ ((Znth j initialized_parents 0) < n_pre)))) (PreH13 : (DSUState n_pre roads (@nil Z) initialized_parents )) ,
  ((( &( "used" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre initialized_parents )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_15 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (initialized_parents: (@list Z)) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (0 <= closest)) (PreH8 : (closest <= 1000000000)) (PreH9 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH10 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH11 : ((Zlength (initialized_parents)) = n_pre)) (PreH12 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((((Znth j initialized_parents 0) = j) /\ (0 <= (Znth j initialized_parents 0))) /\ ((Znth j initialized_parents 0) < n_pre)))) (PreH13 : (DSUState n_pre roads (@nil Z) initialized_parents )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "used" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int64  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre initialized_parents )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (selected: (@list Z)) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (closest: Z) (sum: Z) (used: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= used)) (PreH12 : (used <= (n_pre - 1 ))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= (200000 * 1000000000 ))) (PreH15 : (0 <= closest)) (PreH16 : (closest <= 1000000000)) (PreH17 : ((Zlength (parent)) = n_pre)) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH19 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH20 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH21 : (DSUState n_pre roads selected parent )) (PreH22 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition solver_safety_wit_17 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (selected: (@list Z)) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (closest: Z) (sum: Z) (used: Z) (i: Z) (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= used)) (PreH12 : (used <= (n_pre - 1 ))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= (200000 * 1000000000 ))) (PreH15 : (0 <= closest)) (PreH16 : (closest <= 1000000000)) (PreH17 : ((Zlength (parent)) = n_pre)) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH19 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH20 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH21 : (DSUState n_pre roads selected parent )) (PreH22 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_18 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> retval_2)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < n_pre)) (PreH4 : ((Zlength (parents_after_2)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after_2 0)) /\ ((Znth i parents_after_2 0) < n_pre)))) (PreH6 : (DSURootsPreserved parents_after parents_after_2 )) (PreH7 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval < n_pre)) (PreH10 : ((Zlength (parents_after)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after 0)) /\ ((Znth i parents_after 0) < n_pre)))) (PreH12 : (DSURootsPreserved parent parents_after )) (PreH13 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 1000000000)) (PreH18 : (Pre n_pre k_pre roads )) (PreH19 : (m_pre = (Zlength (roads)))) (PreH20 : ((n_pre - 1 ) <= m_pre)) (PreH21 : (0 <= i_2)) (PreH22 : (i_2 < m_pre)) (PreH23 : (0 <= used)) (PreH24 : (used < (n_pre - 1 ))) (PreH25 : (0 <= sum)) (PreH26 : (sum <= (200000 * 1000000000 ))) (PreH27 : (0 <= closest)) (PreH28 : (closest <= 1000000000)) (PreH29 : ((Zlength (parent)) = n_pre)) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH31 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH32 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH33 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH34 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH35 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH36 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH37 : (DSUState n_pre roads selected parent )) (PreH38 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  ((( &( "b" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ ((used + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (used + 1 )) ”
.

Definition solver_safety_wit_19 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (retval <> retval_2)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < n_pre)) (PreH5 : ((Zlength (parents_after_2)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH7 : (DSURootsPreserved parents_after parents_after_2 )) (PreH8 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH9 : (0 <= retval)) (PreH10 : (retval < n_pre)) (PreH11 : ((Zlength (parents_after)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH13 : (DSURootsPreserved parent parents_after )) (PreH14 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 1000000000)) (PreH19 : (Pre n_pre k_pre roads )) (PreH20 : (m_pre = (Zlength (roads)))) (PreH21 : ((n_pre - 1 ) <= m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < m_pre)) (PreH24 : (0 <= used)) (PreH25 : (used < (n_pre - 1 ))) (PreH26 : (0 <= sum)) (PreH27 : (sum <= (200000 * 1000000000 ))) (PreH28 : (0 <= closest)) (PreH29 : (closest <= 1000000000)) (PreH30 : ((Zlength (parent)) = n_pre)) (PreH31 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH32 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH33 : (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH34 : ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH35 : (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH36 : ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH37 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH38 : (DSUState n_pre roads selected parent )) (PreH39 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  ((( &( "b" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> (used + 1 ))
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ ((sum + ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (sum + ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) )) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (retval <> retval_2)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < n_pre)) (PreH5 : ((Zlength (parents_after_2)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH7 : (DSURootsPreserved parents_after parents_after_2 )) (PreH8 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH9 : (0 <= retval)) (PreH10 : (retval < n_pre)) (PreH11 : ((Zlength (parents_after)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH13 : (DSURootsPreserved parent parents_after )) (PreH14 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 1000000000)) (PreH19 : (Pre n_pre k_pre roads )) (PreH20 : (m_pre = (Zlength (roads)))) (PreH21 : ((n_pre - 1 ) <= m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < m_pre)) (PreH24 : (0 <= used)) (PreH25 : (used < (n_pre - 1 ))) (PreH26 : (0 <= sum)) (PreH27 : (sum <= (200000 * 1000000000 ))) (PreH28 : (0 <= closest)) (PreH29 : (closest <= 1000000000)) (PreH30 : ((Zlength (parent)) = n_pre)) (PreH31 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH32 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH33 : (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH34 : ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH35 : (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH36 : ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH37 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH38 : (DSUState n_pre roads selected parent )) (PreH39 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  ((( &( "b" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> (used + 1 ))
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ ((sum + ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (sum + ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) )) ”
).

Definition solver_safety_wit_19_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (retval <> retval_2)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < n_pre)) (PreH5 : ((Zlength (parents_after_2)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH7 : (DSURootsPreserved parents_after parents_after_2 )) (PreH8 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH9 : (0 <= retval)) (PreH10 : (retval < n_pre)) (PreH11 : ((Zlength (parents_after)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH13 : (DSURootsPreserved parent parents_after )) (PreH14 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 1000000000)) (PreH19 : (Pre n_pre k_pre roads )) (PreH20 : (m_pre = (Zlength (roads)))) (PreH21 : ((n_pre - 1 ) <= m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < m_pre)) (PreH24 : (0 <= used)) (PreH25 : (used < (n_pre - 1 ))) (PreH26 : (0 <= sum)) (PreH27 : (sum <= (200000 * 1000000000 ))) (PreH28 : (0 <= closest)) (PreH29 : (closest <= 1000000000)) (PreH30 : ((Zlength (parent)) = n_pre)) (PreH31 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH32 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH33 : (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH34 : ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH35 : (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH36 : ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH37 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH38 : (DSUState n_pre roads selected parent )) (PreH39 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  ((( &( "b" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> (used + 1 ))
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ ((sum + ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) <= INT64_MAX) ”
.

Definition solver_safety_wit_19_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (retval <> retval_2)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < n_pre)) (PreH5 : ((Zlength (parents_after_2)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH7 : (DSURootsPreserved parents_after parents_after_2 )) (PreH8 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH9 : (0 <= retval)) (PreH10 : (retval < n_pre)) (PreH11 : ((Zlength (parents_after)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH13 : (DSURootsPreserved parent parents_after )) (PreH14 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 1000000000)) (PreH19 : (Pre n_pre k_pre roads )) (PreH20 : (m_pre = (Zlength (roads)))) (PreH21 : ((n_pre - 1 ) <= m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < m_pre)) (PreH24 : (0 <= used)) (PreH25 : (used < (n_pre - 1 ))) (PreH26 : (0 <= sum)) (PreH27 : (sum <= (200000 * 1000000000 ))) (PreH28 : (0 <= closest)) (PreH29 : (closest <= 1000000000)) (PreH30 : ((Zlength (parent)) = n_pre)) (PreH31 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH32 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH33 : (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH34 : ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH35 : (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH36 : ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH37 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH38 : (DSUState n_pre roads selected parent )) (PreH39 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  ((( &( "b" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> (used + 1 ))
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ ((INT64_MIN) <= (sum + ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) )) ”
.

Definition solver_safety_wit_20 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (retval <> retval_2)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < n_pre)) (PreH5 : ((Zlength (parents_after_2)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH7 : (DSURootsPreserved parents_after parents_after_2 )) (PreH8 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH9 : (0 <= retval)) (PreH10 : (retval < n_pre)) (PreH11 : ((Zlength (parents_after)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH13 : (DSURootsPreserved parent parents_after )) (PreH14 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 1000000000)) (PreH19 : (Pre n_pre k_pre roads )) (PreH20 : (m_pre = (Zlength (roads)))) (PreH21 : ((n_pre - 1 ) <= m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < m_pre)) (PreH24 : (0 <= used)) (PreH25 : (used < (n_pre - 1 ))) (PreH26 : (0 <= sum)) (PreH27 : (sum <= (200000 * 1000000000 ))) (PreH28 : (0 <= closest)) (PreH29 : (closest <= 1000000000)) (PreH30 : ((Zlength (parent)) = n_pre)) (PreH31 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH32 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH33 : (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH34 : ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH35 : (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH36 : ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH37 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH38 : (DSUState n_pre roads selected parent )) (PreH39 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  ((( &( "b" ) )) # Int  |-> retval_2)
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> (used + 1 ))
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ (((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - k_pre )) ”
.

Definition solver_safety_wit_21 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (retval <> retval_2)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < n_pre)) (PreH5 : ((Zlength (parents_after_2)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH7 : (DSURootsPreserved parents_after parents_after_2 )) (PreH8 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH9 : (0 <= retval)) (PreH10 : (retval < n_pre)) (PreH11 : ((Zlength (parents_after)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH13 : (DSURootsPreserved parent parents_after )) (PreH14 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 1000000000)) (PreH19 : (Pre n_pre k_pre roads )) (PreH20 : (m_pre = (Zlength (roads)))) (PreH21 : ((n_pre - 1 ) <= m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < m_pre)) (PreH24 : (0 <= used)) (PreH25 : (used < (n_pre - 1 ))) (PreH26 : (0 <= sum)) (PreH27 : (sum <= (200000 * 1000000000 ))) (PreH28 : (0 <= closest)) (PreH29 : (closest <= 1000000000)) (PreH30 : ((Zlength (parent)) = n_pre)) (PreH31 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH32 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH33 : (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH34 : ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH35 : (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH36 : ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH37 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH38 : (DSUState n_pre roads selected parent )) (PreH39 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> (used + 1 ))
  **  ((( &( "sum" ) )) # Int64  |-> (sum + ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) ))
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_22 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH2 : (retval <> retval_2)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < n_pre)) (PreH5 : ((Zlength (parents_after_2)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH7 : (DSURootsPreserved parents_after parents_after_2 )) (PreH8 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH9 : (0 <= retval)) (PreH10 : (retval < n_pre)) (PreH11 : ((Zlength (parents_after)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH13 : (DSURootsPreserved parent parents_after )) (PreH14 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 1000000000)) (PreH19 : (Pre n_pre k_pre roads )) (PreH20 : (m_pre = (Zlength (roads)))) (PreH21 : ((n_pre - 1 ) <= m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < m_pre)) (PreH24 : (0 <= used)) (PreH25 : (used < (n_pre - 1 ))) (PreH26 : (0 <= sum)) (PreH27 : (sum <= (200000 * 1000000000 ))) (PreH28 : (0 <= closest)) (PreH29 : (closest <= 1000000000)) (PreH30 : ((Zlength (parent)) = n_pre)) (PreH31 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH32 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH33 : (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH34 : ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH35 : (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH36 : ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH37 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH38 : (DSUState n_pre roads selected parent )) (PreH39 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> (used + 1 ))
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_23 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval = retval_2)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < n_pre)) (PreH4 : ((Zlength (parents_after_2)) = n_pre)) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH6 : (DSURootsPreserved parents_after parents_after_2 )) (PreH7 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval < n_pre)) (PreH10 : ((Zlength (parents_after)) = n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH12 : (DSURootsPreserved parent parents_after )) (PreH13 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 1000000000)) (PreH18 : (Pre n_pre k_pre roads )) (PreH19 : (m_pre = (Zlength (roads)))) (PreH20 : ((n_pre - 1 ) <= m_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < m_pre)) (PreH23 : (0 <= used)) (PreH24 : (used < (n_pre - 1 ))) (PreH25 : (0 <= sum)) (PreH26 : (sum <= (200000 * 1000000000 ))) (PreH27 : (0 <= closest)) (PreH28 : (closest <= 1000000000)) (PreH29 : ((Zlength (parent)) = n_pre)) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH31 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH32 : (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH33 : ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH34 : (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH35 : ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH36 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH37 : (DSUState n_pre roads selected parent )) (PreH38 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (IntArray.full p n_pre parents_after_2 )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_24 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (sum <> 0)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= processed)) (PreH5 : (processed <= m_pre)) (PreH6 : (used = (n_pre - 1 ))) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (200000 * 1000000000 ))) (PreH9 : (0 <= closest)) (PreH10 : (closest <= 1000000000)) (PreH11 : ((Zlength (parent)) = n_pre)) (PreH12 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH13 : (RoadEncoding sorted_roads sorted_raw )) (PreH14 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH15 : (DSUState n_pre roads selected parent )) (PreH16 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH17 : (sum = 0)) (PreH18 : (Spec n_pre k_pre roads closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ False ”
.

Definition solver_safety_wit_25 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (sum = 0)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= processed)) (PreH5 : (processed <= m_pre)) (PreH6 : (used = (n_pre - 1 ))) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (200000 * 1000000000 ))) (PreH9 : (0 <= closest)) (PreH10 : (closest <= 1000000000)) (PreH11 : ((Zlength (parent)) = n_pre)) (PreH12 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH13 : (RoadEncoding sorted_roads sorted_raw )) (PreH14 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH15 : (DSUState n_pre roads selected parent )) (PreH16 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH17 : (sum <> 0)) (PreH18 : (Spec n_pre k_pre roads sum )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ False ”
.

Definition solver_entail_wit_1 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (EdgeAllocationFits m_pre )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH9 : (Pre n_pre k_pre roads )) (PreH10 : (m_pre = (Zlength (roads)))) ,
  (EdgeArray.undef_full retval m_pre )
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (0 <= (Z.shiftl 1 62)) ” 
  &&  “ (ClosestRoadPrefix k_pre roads 0 (Z.shiftl 1 62) ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full retval 0 (sublist (0) (0) (roads)) )
  **  (EdgeArray.undef_full (retval + (0 * sizeof( "<anonymous struct>" ))) (m_pre - 0 ) )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (EdgeAllocationFits m_pre )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH9 : (Pre n_pre k_pre roads )) (PreH10 : (m_pre = (Zlength (roads)))) ,
  (EdgeArray.undef_full retval m_pre )
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (ClosestRoadPrefix k_pre roads 0 (Z.shiftl 1 62) ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full retval 0 (sublist (0) (0) (roads)) )
  **  (EdgeArray.undef_full (retval + (0 * sizeof( "<anonymous struct>" ))) (m_pre - 0 ) )
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (EdgeAllocationFits m_pre )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH9 : (Pre n_pre k_pre roads )) (PreH10 : (m_pre = (Zlength (roads)))) ,
  (EdgeArray.undef_full retval m_pre )
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (ClosestRoadPrefix k_pre roads 0 (Z.shiftl 1 62) ) ”
.

Definition solver_entail_wit_1_split_goal_spatial := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> 0)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (EdgeAllocationFits m_pre )) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH9 : (Pre n_pre k_pre roads )) (PreH10 : (m_pre = (Zlength (roads)))) ,
  (EdgeArray.undef_full retval m_pre )
  **  (EdgeArray.full input_pre m_pre roads )
|--
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full retval 0 (sublist (0) (0) (roads)) )
  **  (EdgeArray.undef_full (retval + (0 * sizeof( "<anonymous struct>" ))) (m_pre - 0 ) )
.

Definition solver_entail_wit_2 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (i: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= closest)) (PreH12 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  (EdgeArray.undef_full (e + (i * sizeof( "<anonymous struct>" ))) (m_pre - i ) )
|--
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (ClosestRoadPrefix k_pre roads i closest ) ”
  &&  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |->_)
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |->_)
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |->_)
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (i: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (i < m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= closest)) (PreH12 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  (EdgeArray.undef_full (e + (i * sizeof( "<anonymous struct>" ))) (m_pre - i ) )
|--
  EX (x_3: Z)  (x_2: Z)  (x: Z) ,
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (ClosestRoadPrefix k_pre roads i closest ) ”
  &&  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> x_3)
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> x_2)
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> x)
  **  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
).

Definition solver_entail_wit_3_1 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH3 : (m_pre = (Zlength (roads)))) (PreH4 : (Pre n_pre k_pre roads )) (PreH5 : (0 <= i)) (PreH6 : (i < m_pre)) (PreH7 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre )) ” 
  &&  “ (ClosestRoadPrefix k_pre roads (i + 1 ) ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (ClosestRoadPrefix k_pre roads (i + 1 ) ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= n_pre) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
).

Definition solver_entail_wit_3_1_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (ClosestRoadPrefix k_pre roads (i + 1 ) ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) ”
.

Definition solver_entail_wit_3_1_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((n_pre - 1 ) <= m_pre) ”
.

Definition solver_entail_wit_3_1_split_goal_3 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (k_pre <= 1000000000) ”
.

Definition solver_entail_wit_3_1_split_goal_4 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (1 <= k_pre) ”
.

Definition solver_entail_wit_3_1_split_goal_5 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (n_pre <= 200000) ”
.

Definition solver_entail_wit_3_1_split_goal_6 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (2 <= n_pre) ”
.

Definition solver_entail_wit_3_1_split_goal_spatial := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
.

Definition solver_entail_wit_3_2 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH3 : (m_pre = (Zlength (roads)))) (PreH4 : (Pre n_pre k_pre roads )) (PreH5 : (0 <= i)) (PreH6 : (i < m_pre)) (PreH7 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= (k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) )) ” 
  &&  “ (ClosestRoadPrefix k_pre roads (i + 1 ) (k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (ClosestRoadPrefix k_pre roads (i + 1 ) (k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) ) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= n_pre) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
).

Definition solver_entail_wit_3_2_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (ClosestRoadPrefix k_pre roads (i + 1 ) (k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) ) ”
.

Definition solver_entail_wit_3_2_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((n_pre - 1 ) <= m_pre) ”
.

Definition solver_entail_wit_3_2_split_goal_3 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (k_pre <= 1000000000) ”
.

Definition solver_entail_wit_3_2_split_goal_4 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (1 <= k_pre) ”
.

Definition solver_entail_wit_3_2_split_goal_5 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (n_pre <= 200000) ”
.

Definition solver_entail_wit_3_2_split_goal_6 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (2 <= n_pre) ”
.

Definition solver_entail_wit_3_2_split_goal_spatial := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) < closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
.

Definition solver_entail_wit_3_3 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH3 : (m_pre = (Zlength (roads)))) (PreH4 : (Pre n_pre k_pre roads )) (PreH5 : (0 <= i)) (PreH6 : (i < m_pre)) (PreH7 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (ClosestRoadPrefix k_pre roads (i + 1 ) closest ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (ClosestRoadPrefix k_pre roads (i + 1 ) closest ) ” 
  &&  “ (0 <= closest) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= n_pre) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
).

Definition solver_entail_wit_3_3_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (ClosestRoadPrefix k_pre roads (i + 1 ) closest ) ”
.

Definition solver_entail_wit_3_3_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (0 <= closest) ”
.

Definition solver_entail_wit_3_3_split_goal_3 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((n_pre - 1 ) <= m_pre) ”
.

Definition solver_entail_wit_3_3_split_goal_4 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (k_pre <= 1000000000) ”
.

Definition solver_entail_wit_3_3_split_goal_5 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (1 <= k_pre) ”
.

Definition solver_entail_wit_3_3_split_goal_6 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (n_pre <= 200000) ”
.

Definition solver_entail_wit_3_3_split_goal_7 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (2 <= n_pre) ”
.

Definition solver_entail_wit_3_3_split_goal_spatial := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - k_pre ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
.

Definition solver_entail_wit_3_4 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH3 : (m_pre = (Zlength (roads)))) (PreH4 : (Pre n_pre k_pre roads )) (PreH5 : (0 <= i)) (PreH6 : (i < m_pre)) (PreH7 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (ClosestRoadPrefix k_pre roads (i + 1 ) closest ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (ClosestRoadPrefix k_pre roads (i + 1 ) closest ) ” 
  &&  “ (0 <= closest) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (2 <= n_pre) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
).

Definition solver_entail_wit_3_4_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (ClosestRoadPrefix k_pre roads (i + 1 ) closest ) ”
.

Definition solver_entail_wit_3_4_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (0 <= closest) ”
.

Definition solver_entail_wit_3_4_split_goal_3 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ ((n_pre - 1 ) <= m_pre) ”
.

Definition solver_entail_wit_3_4_split_goal_4 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (k_pre <= 1000000000) ”
.

Definition solver_entail_wit_3_4_split_goal_5 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (1 <= k_pre) ”
.

Definition solver_entail_wit_3_4_split_goal_6 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (n_pre <= 200000) ”
.

Definition solver_entail_wit_3_4_split_goal_7 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  “ (2 <= n_pre) ”
.

Definition solver_entail_wit_3_4_split_goal_spatial := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (i: Z) (closest: Z) (e: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((k_pre - (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) ) >= closest)) (PreH8 : ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH9 : (m_pre = (Zlength (roads)))) (PreH10 : (Pre n_pre k_pre roads )) (PreH11 : (0 <= i)) (PreH12 : (i < m_pre)) (PreH13 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.missing_i input_pre i 0 m_pre roads )
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((input_pre + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) ((m_pre - i ) - 1 ) )
|--
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e (i + 1 ) (sublist (0) ((i + 1 )) (roads)) )
  **  (EdgeArray.undef_full (e + ((i + 1 ) * sizeof( "<anonymous struct>" ))) (m_pre - (i + 1 ) ) )
.

Definition solver_entail_wit_4 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= closest)) (PreH12 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  (EdgeArray.undef_full (e + (i * sizeof( "<anonymous struct>" ))) (m_pre - i ) )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre roads )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= closest)) (PreH12 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  (EdgeArray.undef_full (e + (i * sizeof( "<anonymous struct>" ))) (m_pre - i ) )
|--
  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (closest <= 1000000000) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre roads )
).

Definition solver_entail_wit_4_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= closest)) (PreH12 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  (EdgeArray.undef_full (e + (i * sizeof( "<anonymous struct>" ))) (m_pre - i ) )
|--
  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ”
.

Definition solver_entail_wit_4_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= closest)) (PreH12 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  (EdgeArray.undef_full (e + (i * sizeof( "<anonymous struct>" ))) (m_pre - i ) )
|--
  “ (closest <= 1000000000) ”
.

Definition solver_entail_wit_4_split_goal_spatial := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (i: Z) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= closest)) (PreH12 : (ClosestRoadPrefix k_pre roads i closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e i (sublist (0) (i) (roads)) )
  **  (EdgeArray.undef_full (e + (i * sizeof( "<anonymous struct>" ))) (m_pre - i ) )
|--
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre roads )
.

Definition solver_entail_wit_5 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (e: Z) (sorted: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (RoadSortResult roads sorted sorted_raw_2 order_2 )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= closest)) (PreH11 : (closest <= 1000000000)) (PreH12 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  (IntArray.undef_full retval n_pre )
  **  (EdgeArray.full e m_pre sorted )
  **  (EdgeArray.full input_pre m_pre roads )
|--
  EX (initialized_parents: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ ((Zlength (initialized_parents)) = 0) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Znth j initialized_parents 0) = j)) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full retval 0 initialized_parents )
  **  (IntArray.undef_seg retval 0 n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (sorted: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (RoadSortResult roads sorted sorted_raw_2 order_2 )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= closest)) (PreH11 : (closest <= 1000000000)) (PreH12 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  TT && emp 
|--
  “ forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Znth j (@nil Z) 0) = j)) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition solver_entail_wit_5_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (sorted: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (RoadSortResult roads sorted sorted_raw_2 order_2 )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= closest)) (PreH11 : (closest <= 1000000000)) (PreH12 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Znth j (@nil Z) 0) = j))
.

Definition solver_entail_wit_5_split_goal_2 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (sorted: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (RoadSortResult roads sorted sorted_raw_2 order_2 )) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= closest)) (PreH11 : (closest <= 1000000000)) (PreH12 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition solver_entail_wit_6 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (initialized_parents_2: (@list Z)) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (closest: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= closest)) (PreH12 : (closest <= 1000000000)) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH15 : ((Zlength (initialized_parents_2)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j initialized_parents_2 0) = j))) ,
  (IntArray.full p (i + 1 ) (app (initialized_parents_2) ((cons (i) ((@nil Z))))) )
  **  (IntArray.undef_seg p (i + 1 ) n_pre )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads_2 )
|--
  EX (initialized_parents: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ ((Zlength (initialized_parents)) = (i + 1 )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth j initialized_parents 0) = j)) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p (i + 1 ) initialized_parents )
  **  (IntArray.undef_seg p (i + 1 ) n_pre )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (initialized_parents_2: (@list Z)) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (closest: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= closest)) (PreH12 : (closest <= 1000000000)) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH15 : ((Zlength (initialized_parents_2)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j initialized_parents_2 0) = j))) ,
  TT && emp 
|--
  “ ((Zlength ((app (initialized_parents_2) ((cons (i) ((@nil Z))))))) = (i + 1 )) ”
  &&  emp
).

Definition solver_entail_wit_6_split_goal_1 := 
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (initialized_parents_2: (@list Z)) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (closest: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= closest)) (PreH12 : (closest <= 1000000000)) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH15 : ((Zlength (initialized_parents_2)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j initialized_parents_2 0) = j))) ,
  ((Zlength ((app (initialized_parents_2) ((cons (i) ((@nil Z))))))) = (i + 1 ))
.

Definition solver_entail_wit_7 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (initialized_parents_2: (@list Z)) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (closest: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= closest)) (PreH12 : (closest <= 1000000000)) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH15 : ((Zlength (initialized_parents_2)) = i)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 initialized_parents_2 0) = j_2))) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads_2 )
  **  (IntArray.full p i initialized_parents_2 )
  **  (IntArray.undef_seg p i n_pre )
|--
  EX (initialized_parents: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z)) ,
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ ((Zlength (initialized_parents)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((((Znth j initialized_parents 0) = j) /\ (0 <= (Znth j initialized_parents 0))) /\ ((Znth j initialized_parents 0) < n_pre))) ” 
  &&  “ (DSUState n_pre roads (@nil Z) initialized_parents ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre initialized_parents )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (initialized_parents_2: (@list Z)) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (closest: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= closest)) (PreH12 : (closest <= 1000000000)) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH15 : ((Zlength (initialized_parents_2)) = i)) (PreH16 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 initialized_parents_2 0) = j_2))) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads_2 )
  **  (IntArray.full p i initialized_parents_2 )
|--
  EX (initialized_parents: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z)) ,
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ ((Zlength (initialized_parents)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((((Znth j initialized_parents 0) = j) /\ (0 <= (Znth j initialized_parents 0))) /\ ((Znth j initialized_parents 0) < n_pre))) ” 
  &&  “ (DSUState n_pre roads (@nil Z) initialized_parents ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre initialized_parents )
).

Definition solver_entail_wit_8 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (initialized_parents: (@list Z)) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (0 <= closest)) (PreH8 : (closest <= 1000000000)) (PreH9 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH10 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH11 : ((Zlength (initialized_parents)) = n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((Znth j_2 initialized_parents 0) = j_2) /\ (0 <= (Znth j_2 initialized_parents 0))) /\ ((Znth j_2 initialized_parents 0) < n_pre)))) (PreH13 : (DSUState n_pre roads (@nil Z) initialized_parents )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads_2 )
  **  (IntArray.full p n_pre initialized_parents )
|--
  EX (selected: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z))  (parent: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order 0 selected 0 0 ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
) \/
(
forall (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (initialized_parents: (@list Z)) (closest: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (0 <= closest)) (PreH8 : (closest <= 1000000000)) (PreH9 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH10 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH11 : ((Zlength (initialized_parents)) = n_pre)) (PreH12 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((((Znth j_2 initialized_parents 0) = j_2) /\ (0 <= (Znth j_2 initialized_parents 0))) /\ ((Znth j_2 initialized_parents 0) < n_pre)))) (PreH13 : (DSUState n_pre roads (@nil Z) initialized_parents )) ,
  TT && emp 
|--
  EX (selected: (@list Z))  (sorted_raw: (@list Z))  (order: (@list Z)) ,
  “ (((Zlength (initialized_parents)) - 1 ) <= (Zlength (roads))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (roads))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((Zlength (initialized_parents)) - 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (200000 * 1000000000 )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (Zlength (initialized_parents)))) -> ((0 <= (Znth j initialized_parents 0)) /\ ((Znth j initialized_parents 0) < (Zlength (initialized_parents))))) ” 
  &&  “ (RoadSortResult roads sorted_roads_2 sorted_raw order ) ” 
  &&  “ (DSUState (Zlength (initialized_parents)) roads selected initialized_parents ) ” 
  &&  “ (KruskalPrefixState (Zlength (initialized_parents)) k_pre roads sorted_roads_2 order 0 selected 0 0 ) ”
  &&  emp
).

Definition solver_entail_wit_9 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z))  __default__Prod__Prod_Z_Z_Z (PreH1 : (used < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= used)) (PreH13 : (used <= (n_pre - 1 ))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= (200000 * 1000000000 ))) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : ((Zlength (parent)) = n_pre)) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent 0)) /\ ((Znth j_2 parent 0) < n_pre)))) (PreH20 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH21 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH22 : (DSUState n_pre roads selected parent )) (PreH23 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
|--
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < m_pre) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used < (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  (IntArray.full p n_pre parent )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z))  __default__Prod__Prod_Z_Z_Z (PreH1 : (used < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= used)) (PreH13 : (used <= (n_pre - 1 ))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= (200000 * 1000000000 ))) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : ((Zlength (parent)) = n_pre)) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent 0)) /\ ((Znth j_2 parent 0) < n_pre)))) (PreH20 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH21 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH22 : (DSUState n_pre roads selected parent )) (PreH23 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
|--
  “ ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
).

Definition solver_entail_wit_9_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z))  __default__Prod__Prod_Z_Z_Z (PreH1 : (used < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= used)) (PreH13 : (used <= (n_pre - 1 ))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= (200000 * 1000000000 ))) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : ((Zlength (parent)) = n_pre)) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent 0)) /\ ((Znth j_2 parent 0) < n_pre)))) (PreH20 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH21 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH22 : (DSUState n_pre roads selected parent )) (PreH23 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
|--
  “ ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ”
.

Definition solver_entail_wit_9_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z))  __default__Prod__Prod_Z_Z_Z (PreH1 : (used < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= used)) (PreH13 : (used <= (n_pre - 1 ))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= (200000 * 1000000000 ))) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : ((Zlength (parent)) = n_pre)) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent 0)) /\ ((Znth j_2 parent 0) < n_pre)))) (PreH20 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH21 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH22 : (DSUState n_pre roads selected parent )) (PreH23 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
|--
  “ (1 <= (ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z)))) ”
.

Definition solver_entail_wit_9_split_goal_3 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z))  __default__Prod__Prod_Z_Z_Z (PreH1 : (used < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= used)) (PreH13 : (used <= (n_pre - 1 ))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= (200000 * 1000000000 ))) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : ((Zlength (parent)) = n_pre)) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent 0)) /\ ((Znth j_2 parent 0) < n_pre)))) (PreH20 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH21 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH22 : (DSUState n_pre roads selected parent )) (PreH23 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
|--
  “ ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ”
.

Definition solver_entail_wit_9_split_goal_4 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z))  __default__Prod__Prod_Z_Z_Z (PreH1 : (used < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= used)) (PreH13 : (used <= (n_pre - 1 ))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= (200000 * 1000000000 ))) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : ((Zlength (parent)) = n_pre)) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent 0)) /\ ((Znth j_2 parent 0) < n_pre)))) (PreH20 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH21 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH22 : (DSUState n_pre roads selected parent )) (PreH23 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
|--
  “ (1 <= (ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z)))) ”
.

Definition solver_entail_wit_9_split_goal_5 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (PreH1 : (used < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= used)) (PreH13 : (used <= (n_pre - 1 ))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= (200000 * 1000000000 ))) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : ((Zlength (parent)) = n_pre)) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent 0)) /\ ((Znth j_2 parent 0) < n_pre)))) (PreH20 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH21 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH22 : (DSUState n_pre roads selected parent )) (PreH23 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
|--
  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ”
.

Definition solver_entail_wit_9_split_goal_spatial := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z))  __default__Prod__Prod_Z_Z_Z (PreH1 : (used < (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= used)) (PreH13 : (used <= (n_pre - 1 ))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= (200000 * 1000000000 ))) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : ((Zlength (parent)) = n_pre)) (PreH19 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent 0)) /\ ((Znth j_2 parent 0) < n_pre)))) (PreH20 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH21 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH22 : (DSUState n_pre roads selected parent )) (PreH23 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
|--
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads __default__Prod__Prod_Z_Z_Z))))
.

Definition solver_entail_wit_10_1 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (parent_2: (@list Z)) (selected_2: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH2 : (retval <> retval_2)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < n_pre)) (PreH5 : ((Zlength (parents_after_2)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH7 : (DSURootsPreserved parents_after parents_after_2 )) (PreH8 : (DSUFindResult n_pre roads selected_2 parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH9 : (0 <= retval)) (PreH10 : (retval < n_pre)) (PreH11 : ((Zlength (parents_after)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH13 : (DSURootsPreserved parent_2 parents_after )) (PreH14 : (DSUFindResult n_pre roads selected_2 parent_2 parents_after ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 1000000000)) (PreH19 : (Pre n_pre k_pre roads )) (PreH20 : (m_pre = (Zlength (roads)))) (PreH21 : ((n_pre - 1 ) <= m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < m_pre)) (PreH24 : (0 <= used)) (PreH25 : (used < (n_pre - 1 ))) (PreH26 : (0 <= sum)) (PreH27 : (sum <= (200000 * 1000000000 ))) (PreH28 : (0 <= closest)) (PreH29 : (closest <= 1000000000)) (PreH30 : ((Zlength (parent_2)) = n_pre)) (PreH31 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent_2 0)) /\ ((Znth j_2 parent_2 0) < n_pre)))) (PreH32 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH33 : (1 <= (ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH34 : ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH35 : (1 <= (ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH36 : ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH37 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH38 : (DSUState n_pre roads selected_2 parent_2 )) (PreH39 : (KruskalPrefixState n_pre k_pre roads sorted_roads_2 order_2 i selected_2 used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads_2 )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))
|--
  EX (selected: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z))  (parent: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= (used + 1 )) ” 
  &&  “ ((used + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (0 <= (sum + ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - k_pre ) )) ” 
  &&  “ ((sum + ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order (i + 1 ) selected (used + 1 ) (sum + ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (parent_2: (@list Z)) (selected_2: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) > k_pre)) (PreH8 : (retval <> retval_2)) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < n_pre)) (PreH11 : ((Zlength (parents_after_2)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH13 : (DSURootsPreserved parents_after parents_after_2 )) (PreH14 : (DSUFindResult n_pre roads selected_2 parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH15 : (0 <= retval)) (PreH16 : (retval < n_pre)) (PreH17 : ((Zlength (parents_after)) = n_pre)) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH19 : (DSURootsPreserved parent_2 parents_after )) (PreH20 : (DSUFindResult n_pre roads selected_2 parent_2 parents_after ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre <= 200000)) (PreH23 : (1 <= k_pre)) (PreH24 : (k_pre <= 1000000000)) (PreH25 : (Pre n_pre k_pre roads )) (PreH26 : (m_pre = (Zlength (roads)))) (PreH27 : ((n_pre - 1 ) <= m_pre)) (PreH28 : (0 <= i)) (PreH29 : (i < m_pre)) (PreH30 : (0 <= used)) (PreH31 : (used < (n_pre - 1 ))) (PreH32 : (0 <= sum)) (PreH33 : (sum <= (200000 * 1000000000 ))) (PreH34 : (0 <= closest)) (PreH35 : (closest <= 1000000000)) (PreH36 : ((Zlength (parent_2)) = n_pre)) (PreH37 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent_2 0)) /\ ((Znth j_2 parent_2 0) < n_pre)))) (PreH38 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH39 : (1 <= (ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH40 : ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH41 : (1 <= (ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH42 : ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH43 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH44 : (DSUState n_pre roads selected_2 parent_2 )) (PreH45 : (KruskalPrefixState n_pre k_pre roads sorted_roads_2 order_2 i selected_2 used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads_2 )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))
|--
  EX (selected: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= (used + 1 )) ” 
  &&  “ ((used + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (0 <= (sum + ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - k_pre ) )) ” 
  &&  “ ((sum + ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength ((replace_Znth (retval) (retval_2) (parents_after_2)))) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j (replace_Znth (retval) (retval_2) (parents_after_2)) 0)) /\ ((Znth j (replace_Znth (retval) (retval_2) (parents_after_2)) 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected (replace_Znth (retval) (retval_2) (parents_after_2)) ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order (i + 1 ) selected (used + 1 ) (sum + ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - k_pre ) ) ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
).

Definition solver_entail_wit_10_2 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (parent_2: (@list Z)) (selected_2: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH2 : (retval <> retval_2)) (PreH3 : (0 <= retval_2)) (PreH4 : (retval_2 < n_pre)) (PreH5 : ((Zlength (parents_after_2)) = n_pre)) (PreH6 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH7 : (DSURootsPreserved parents_after parents_after_2 )) (PreH8 : (DSUFindResult n_pre roads selected_2 parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH9 : (0 <= retval)) (PreH10 : (retval < n_pre)) (PreH11 : ((Zlength (parents_after)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH13 : (DSURootsPreserved parent_2 parents_after )) (PreH14 : (DSUFindResult n_pre roads selected_2 parent_2 parents_after ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH15 : (2 <= n_pre)) (PreH16 : (n_pre <= 200000)) (PreH17 : (1 <= k_pre)) (PreH18 : (k_pre <= 1000000000)) (PreH19 : (Pre n_pre k_pre roads )) (PreH20 : (m_pre = (Zlength (roads)))) (PreH21 : ((n_pre - 1 ) <= m_pre)) (PreH22 : (0 <= i)) (PreH23 : (i < m_pre)) (PreH24 : (0 <= used)) (PreH25 : (used < (n_pre - 1 ))) (PreH26 : (0 <= sum)) (PreH27 : (sum <= (200000 * 1000000000 ))) (PreH28 : (0 <= closest)) (PreH29 : (closest <= 1000000000)) (PreH30 : ((Zlength (parent_2)) = n_pre)) (PreH31 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent_2 0)) /\ ((Znth j_2 parent_2 0) < n_pre)))) (PreH32 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH33 : (1 <= (ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH34 : ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH35 : (1 <= (ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH36 : ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH37 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH38 : (DSUState n_pre roads selected_2 parent_2 )) (PreH39 : (KruskalPrefixState n_pre k_pre roads sorted_roads_2 order_2 i selected_2 used sum )) ,
  (IntArray.full p n_pre (replace_Znth (retval) (retval_2) (parents_after_2)) )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads_2 )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))
|--
  EX (selected: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z))  (parent: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= (used + 1 )) ” 
  &&  “ ((used + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order (i + 1 ) selected (used + 1 ) sum ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (parent_2: (@list Z)) (selected_2: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= k_pre)) (PreH8 : (retval <> retval_2)) (PreH9 : (0 <= retval_2)) (PreH10 : (retval_2 < n_pre)) (PreH11 : ((Zlength (parents_after_2)) = n_pre)) (PreH12 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH13 : (DSURootsPreserved parents_after parents_after_2 )) (PreH14 : (DSUFindResult n_pre roads selected_2 parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH15 : (0 <= retval)) (PreH16 : (retval < n_pre)) (PreH17 : ((Zlength (parents_after)) = n_pre)) (PreH18 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH19 : (DSURootsPreserved parent_2 parents_after )) (PreH20 : (DSUFindResult n_pre roads selected_2 parent_2 parents_after ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre <= 200000)) (PreH23 : (1 <= k_pre)) (PreH24 : (k_pre <= 1000000000)) (PreH25 : (Pre n_pre k_pre roads )) (PreH26 : (m_pre = (Zlength (roads)))) (PreH27 : ((n_pre - 1 ) <= m_pre)) (PreH28 : (0 <= i)) (PreH29 : (i < m_pre)) (PreH30 : (0 <= used)) (PreH31 : (used < (n_pre - 1 ))) (PreH32 : (0 <= sum)) (PreH33 : (sum <= (200000 * 1000000000 ))) (PreH34 : (0 <= closest)) (PreH35 : (closest <= 1000000000)) (PreH36 : ((Zlength (parent_2)) = n_pre)) (PreH37 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent_2 0)) /\ ((Znth j_2 parent_2 0) < n_pre)))) (PreH38 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH39 : (1 <= (ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH40 : ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH41 : (1 <= (ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH42 : ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH43 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH44 : (DSUState n_pre roads selected_2 parent_2 )) (PreH45 : (KruskalPrefixState n_pre k_pre roads sorted_roads_2 order_2 i selected_2 used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads_2 )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))
|--
  EX (selected: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= (used + 1 )) ” 
  &&  “ ((used + 1 ) <= (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength ((replace_Znth (retval) (retval_2) (parents_after_2)))) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j (replace_Znth (retval) (retval_2) (parents_after_2)) 0)) /\ ((Znth j (replace_Znth (retval) (retval_2) (parents_after_2)) 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected (replace_Znth (retval) (retval_2) (parents_after_2)) ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order (i + 1 ) selected (used + 1 ) sum ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
).

Definition solver_entail_wit_10_3 := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (parent_2: (@list Z)) (selected_2: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval = retval_2)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < n_pre)) (PreH4 : ((Zlength (parents_after_2)) = n_pre)) (PreH5 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH6 : (DSURootsPreserved parents_after parents_after_2 )) (PreH7 : (DSUFindResult n_pre roads selected_2 parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval < n_pre)) (PreH10 : ((Zlength (parents_after)) = n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH12 : (DSURootsPreserved parent_2 parents_after )) (PreH13 : (DSUFindResult n_pre roads selected_2 parent_2 parents_after ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 1000000000)) (PreH18 : (Pre n_pre k_pre roads )) (PreH19 : (m_pre = (Zlength (roads)))) (PreH20 : ((n_pre - 1 ) <= m_pre)) (PreH21 : (0 <= i)) (PreH22 : (i < m_pre)) (PreH23 : (0 <= used)) (PreH24 : (used < (n_pre - 1 ))) (PreH25 : (0 <= sum)) (PreH26 : (sum <= (200000 * 1000000000 ))) (PreH27 : (0 <= closest)) (PreH28 : (closest <= 1000000000)) (PreH29 : ((Zlength (parent_2)) = n_pre)) (PreH30 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent_2 0)) /\ ((Znth j_2 parent_2 0) < n_pre)))) (PreH31 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH32 : (1 <= (ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH33 : ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH34 : (1 <= (ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH35 : ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH36 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH37 : (DSUState n_pre roads selected_2 parent_2 )) (PreH38 : (KruskalPrefixState n_pre k_pre roads sorted_roads_2 order_2 i selected_2 used sum )) ,
  (IntArray.full p n_pre parents_after_2 )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads_2 )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))
|--
  EX (selected: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z))  (parent: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order (i + 1 ) selected used sum ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads_2: (@list ((Z * Z) * Z))) (sorted_raw_2: (@list Z)) (order_2: (@list Z)) (parent_2: (@list Z)) (selected_2: (@list Z)) (i: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : ((ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH3 : (((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH4 : (((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH5 : (((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH6 : (((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH7 : (retval = retval_2)) (PreH8 : (0 <= retval_2)) (PreH9 : (retval_2 < n_pre)) (PreH10 : ((Zlength (parents_after_2)) = n_pre)) (PreH11 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after_2 0)) /\ ((Znth i_2 parents_after_2 0) < n_pre)))) (PreH12 : (DSURootsPreserved parents_after parents_after_2 )) (PreH13 : (DSUFindResult n_pre roads selected_2 parents_after parents_after_2 ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH14 : (0 <= retval)) (PreH15 : (retval < n_pre)) (PreH16 : ((Zlength (parents_after)) = n_pre)) (PreH17 : forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((0 <= (Znth i_2 parents_after 0)) /\ ((Znth i_2 parents_after 0) < n_pre)))) (PreH18 : (DSURootsPreserved parent_2 parents_after )) (PreH19 : (DSUFindResult n_pre roads selected_2 parent_2 parents_after ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH20 : (2 <= n_pre)) (PreH21 : (n_pre <= 200000)) (PreH22 : (1 <= k_pre)) (PreH23 : (k_pre <= 1000000000)) (PreH24 : (Pre n_pre k_pre roads )) (PreH25 : (m_pre = (Zlength (roads)))) (PreH26 : ((n_pre - 1 ) <= m_pre)) (PreH27 : (0 <= i)) (PreH28 : (i < m_pre)) (PreH29 : (0 <= used)) (PreH30 : (used < (n_pre - 1 ))) (PreH31 : (0 <= sum)) (PreH32 : (sum <= (200000 * 1000000000 ))) (PreH33 : (0 <= closest)) (PreH34 : (closest <= 1000000000)) (PreH35 : ((Zlength (parent_2)) = n_pre)) (PreH36 : forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((0 <= (Znth j_2 parent_2 0)) /\ ((Znth j_2 parent_2 0) < n_pre)))) (PreH37 : (RoadSortResult roads sorted_roads_2 sorted_raw_2 order_2 )) (PreH38 : (1 <= (ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH39 : ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH40 : (1 <= (ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))) (PreH41 : ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH42 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH43 : (DSUState n_pre roads selected_2 parent_2 )) (PreH44 : (KruskalPrefixState n_pre k_pre roads sorted_roads_2 order_2 i selected_2 used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i 0 m_pre sorted_roads_2 )
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i sorted_roads_2 __default__Prod__Prod_Z_Z_Z))))
|--
  EX (selected: (@list Z))  (sorted_roads: (@list ((Z * Z) * Z)))  (sorted_raw: (@list Z))  (order: (@list Z)) ,
  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= m_pre) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parents_after_2)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parents_after_2 0)) /\ ((Znth j parents_after_2 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parents_after_2 ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order (i + 1 ) selected used sum ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
).

Definition solver_entail_wit_11_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (PreH1 : (i >= m_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= m_pre)) (PreH11 : (0 <= used)) (PreH12 : (used <= (n_pre - 1 ))) (PreH13 : (0 <= sum)) (PreH14 : (sum <= (200000 * 1000000000 ))) (PreH15 : (0 <= closest)) (PreH16 : (closest <= 1000000000)) (PreH17 : ((Zlength (parent)) = n_pre)) (PreH18 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH19 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH20 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH21 : (DSUState n_pre roads selected parent )) (PreH22 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
|--
  (EX (processed: Z) ,
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= processed) ” 
  &&  “ (processed <= m_pre) ” 
  &&  “ (used = (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (RoadEncoding sorted_roads sorted_raw ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum ) ” 
  &&  “ (sum <> 0) ” 
  &&  “ (Spec n_pre k_pre roads sum ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre ))
  ||
  (EX (processed: Z) ,
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= processed) ” 
  &&  “ (processed <= m_pre) ” 
  &&  “ (used = (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (RoadEncoding sorted_roads sorted_raw ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum ) ” 
  &&  “ (sum = 0) ” 
  &&  “ (Spec n_pre k_pre roads closest ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre ))
.

Definition solver_entail_wit_11_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (closest: Z) (sum: Z) (used: Z) (i: Z) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (PreH1 : (used >= (n_pre - 1 ))) (PreH2 : (i < m_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 1000000000)) (PreH7 : (Pre n_pre k_pre roads )) (PreH8 : (m_pre = (Zlength (roads)))) (PreH9 : ((n_pre - 1 ) <= m_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= m_pre)) (PreH12 : (0 <= used)) (PreH13 : (used <= (n_pre - 1 ))) (PreH14 : (0 <= sum)) (PreH15 : (sum <= (200000 * 1000000000 ))) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : ((Zlength (parent)) = n_pre)) (PreH19 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH20 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH21 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH22 : (DSUState n_pre roads selected parent )) (PreH23 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
|--
  (EX (processed: Z) ,
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= processed) ” 
  &&  “ (processed <= m_pre) ” 
  &&  “ (used = (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (RoadEncoding sorted_roads sorted_raw ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum ) ” 
  &&  “ (sum <> 0) ” 
  &&  “ (Spec n_pre k_pre roads sum ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre ))
  ||
  (EX (processed: Z) ,
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= processed) ” 
  &&  “ (processed <= m_pre) ” 
  &&  “ (used = (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (RoadEncoding sorted_roads sorted_raw ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum ) ” 
  &&  “ (sum = 0) ” 
  &&  “ (Spec n_pre k_pre roads closest ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre ))
.

Definition solver_return_wit_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (PreH1 : (sum <> 0)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= processed)) (PreH5 : (processed <= m_pre)) (PreH6 : (used = (n_pre - 1 ))) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (200000 * 1000000000 ))) (PreH9 : (0 <= closest)) (PreH10 : (closest <= 1000000000)) (PreH11 : ((Zlength (parent)) = n_pre)) (PreH12 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH13 : (RoadEncoding sorted_roads sorted_raw )) (PreH14 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH15 : (DSUState n_pre roads selected parent )) (PreH16 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH17 : (sum <> 0)) (PreH18 : (Spec n_pre k_pre roads sum )) ,
  (EdgeArray.full input_pre m_pre roads )
|--
  “ (Spec n_pre k_pre roads sum ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
.

Definition solver_return_wit_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (PreH1 : (sum = 0)) (PreH2 : (m_pre = (Zlength (roads)))) (PreH3 : (Pre n_pre k_pre roads )) (PreH4 : (0 <= processed)) (PreH5 : (processed <= m_pre)) (PreH6 : (used = (n_pre - 1 ))) (PreH7 : (0 <= sum)) (PreH8 : (sum <= (200000 * 1000000000 ))) (PreH9 : (0 <= closest)) (PreH10 : (closest <= 1000000000)) (PreH11 : ((Zlength (parent)) = n_pre)) (PreH12 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH13 : (RoadEncoding sorted_roads sorted_raw )) (PreH14 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH15 : (DSUState n_pre roads selected parent )) (PreH16 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH17 : (sum = 0)) (PreH18 : (Spec n_pre k_pre roads closest )) ,
  (EdgeArray.full input_pre m_pre roads )
|--
  “ (Spec n_pre k_pre roads closest ) ”
  &&  (EdgeArray.full input_pre m_pre roads )
.

Definition solver_partial_solve_wit_1_pure := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z)))  __default__Prod__Prod_Z_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (EdgeAllocationFits m_pre )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH8 : (Pre n_pre k_pre roads )) (PreH9 : (m_pre = (Zlength (roads)))) ,
  ((( &( "e" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (0 <= m_pre) ” 
  &&  “ (EdgeAllocationSize (unsigned_last_nbits ((m_pre * sizeof( "<anonymous struct>" ) )) (32)) m_pre ) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z)))  __default__Prod__Prod_Z_Z_Z (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (EdgeAllocationFits m_pre )) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH13 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (m_pre = (Zlength (roads)))) ,
  ((( &( "e" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (EdgeAllocationSize (unsigned_last_nbits ((m_pre * sizeof( "<anonymous struct>" ) )) (32)) m_pre ) ”
).

Definition solver_partial_solve_wit_1_pure_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z)))  __default__Prod__Prod_Z_Z_Z (PreH1 : (k_pre <= INT64_MAX)) (PreH2 : (k_pre >= INT64_MIN)) (PreH3 : (m_pre <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (m_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (EdgeAllocationFits m_pre )) (PreH10 : (1 <= k_pre)) (PreH11 : (k_pre <= 1000000000)) (PreH12 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH13 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (m_pre = (Zlength (roads)))) ,
  ((( &( "e" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (EdgeAllocationSize (unsigned_last_nbits ((m_pre * sizeof( "<anonymous struct>" ) )) (32)) m_pre ) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z)))  __default__Prod__Prod_Z_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (EdgeAllocationFits m_pre )) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : ((n_pre - 1 ) <= (Zlength (roads)))) (PreH7 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000)))) (PreH8 : (Pre n_pre k_pre roads )) (PreH9 : (m_pre = (Zlength (roads)))) ,
  (EdgeArray.full input_pre m_pre roads )
|--
  “ (0 <= m_pre) ” 
  &&  “ (EdgeAllocationSize (unsigned_last_nbits ((m_pre * sizeof( "<anonymous struct>" ) )) (32)) m_pre ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (EdgeAllocationFits m_pre ) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ ((n_pre - 1 ) <= (Zlength (roads))) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (roads)))) -> ((((((1 <= (ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z)))) /\ ((ztriple_1 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_2 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) /\ (1 <= (ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))))) /\ ((ztriple_3 ((Znth i roads __default__Prod__Prod_Z_Z_Z))) <= 1000000000))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ”
  &&  (EdgeArray.full input_pre m_pre roads )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2_pure := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (e: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre n_pre k_pre roads )) (PreH6 : (m_pre = (Zlength (roads)))) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre roads )
|--
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (EdgeAllocationSize sizeof( "<anonymous struct>" ) 1 ) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (e: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (k_pre <= INT64_MAX)) (PreH3 : (closest >= INT64_MIN)) (PreH4 : (k_pre >= INT64_MIN)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (Pre n_pre k_pre roads )) (PreH14 : (m_pre = (Zlength (roads)))) (PreH15 : ((n_pre - 1 ) <= m_pre)) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre roads )
|--
  “ (EdgeAllocationSize sizeof( "<anonymous struct>" ) 1 ) ”
).

Definition solver_partial_solve_wit_2_pure_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (e: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (k_pre <= INT64_MAX)) (PreH3 : (closest >= INT64_MIN)) (PreH4 : (k_pre >= INT64_MIN)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : (m_pre >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (2 <= n_pre)) (PreH10 : (n_pre <= 200000)) (PreH11 : (1 <= k_pre)) (PreH12 : (k_pre <= 1000000000)) (PreH13 : (Pre n_pre k_pre roads )) (PreH14 : (m_pre = (Zlength (roads)))) (PreH15 : ((n_pre - 1 ) <= m_pre)) (PreH16 : (0 <= closest)) (PreH17 : (closest <= 1000000000)) (PreH18 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre roads )
|--
  “ (EdgeAllocationSize sizeof( "<anonymous struct>" ) 1 ) ”
.

Definition solver_partial_solve_wit_2_aux := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (e: Z) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre n_pre k_pre roads )) (PreH6 : (m_pre = (Zlength (roads)))) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre roads )
|--
  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (EdgeAllocationSize sizeof( "<anonymous struct>" ) 1 ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ”
  &&  (EdgeArray.full e m_pre roads )
  **  (EdgeArray.full input_pre m_pre roads )
.

Definition solver_partial_solve_wit_2 := solver_partial_solve_wit_2_pure -> solver_partial_solve_wit_2_aux.

Definition solver_partial_solve_wit_3_pure := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (e: Z) (sorted: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (PreH1 : (RoadSortResult roads sorted sorted_raw order )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= closest)) (PreH10 : (closest <= 1000000000)) (PreH11 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  ((( &( "p" ) )) # Ptr  |->_)
  **  (EdgeArray.full e m_pre sorted )
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ”
.

Definition solver_partial_solve_wit_3_aux := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (closest: Z) (e: Z) (sorted: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (PreH1 : (RoadSortResult roads sorted sorted_raw order )) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= closest)) (PreH10 : (closest <= 1000000000)) (PreH11 : (ClosestRoadPrefix k_pre roads m_pre closest )) ,
  (EdgeArray.full e m_pre sorted )
  **  (EdgeArray.full input_pre m_pre roads )
|--
  “ (0 <= n_pre) ” 
  &&  “ ((n_pre * sizeof(INT) ) = (n_pre * sizeof(INT) )) ” 
  &&  “ (RoadSortResult roads sorted sorted_raw order ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ”
  &&  (EdgeArray.full e m_pre sorted )
  **  (EdgeArray.full input_pre m_pre roads )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (p: Z) (e: Z) (initialized_parents: (@list Z)) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (closest: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 1000000000)) (PreH6 : (Pre n_pre k_pre roads )) (PreH7 : (m_pre = (Zlength (roads)))) (PreH8 : ((n_pre - 1 ) <= m_pre)) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (0 <= closest)) (PreH12 : (closest <= 1000000000)) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH15 : ((Zlength (initialized_parents)) = i)) (PreH16 : forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j initialized_parents 0) = j))) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p i initialized_parents )
  **  (IntArray.undef_seg p i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ ((Zlength (initialized_parents)) = i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j initialized_parents 0) = j)) ”
  &&  (((p + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg p (i + 1 ) n_pre )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p i initialized_parents )
.

Definition solver_partial_solve_wit_5_pure := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre n_pre k_pre roads )) (PreH6 : (m_pre = (Zlength (roads)))) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < m_pre)) (PreH10 : (0 <= used)) (PreH11 : (used < (n_pre - 1 ))) (PreH12 : (0 <= sum)) (PreH13 : (sum <= (200000 * 1000000000 ))) (PreH14 : (0 <= closest)) (PreH15 : (closest <= 1000000000)) (PreH16 : ((Zlength (parent)) = n_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH18 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH19 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH20 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH21 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH22 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH23 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH24 : (DSUState n_pre roads selected parent )) (PreH25 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ (0 <= ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 )) ” 
  &&  “ (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) < n_pre) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parent 0)) /\ ((Znth i parent 0) < n_pre))) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : (closest <= INT64_MAX)) (PreH3 : (sum <= INT64_MAX)) (PreH4 : (k_pre <= INT64_MAX)) (PreH5 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH6 : (closest >= INT64_MIN)) (PreH7 : (sum >= INT64_MIN)) (PreH8 : (k_pre >= INT64_MIN)) (PreH9 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH10 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH11 : (used <= INT_MAX)) (PreH12 : (i_2 <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH16 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH17 : (used >= INT_MIN)) (PreH18 : (i_2 >= INT_MIN)) (PreH19 : (m_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre <= 200000)) (PreH23 : (1 <= k_pre)) (PreH24 : (k_pre <= 1000000000)) (PreH25 : (Pre n_pre k_pre roads )) (PreH26 : (m_pre = (Zlength (roads)))) (PreH27 : ((n_pre - 1 ) <= m_pre)) (PreH28 : (0 <= i_2)) (PreH29 : (i_2 < m_pre)) (PreH30 : (0 <= used)) (PreH31 : (used < (n_pre - 1 ))) (PreH32 : (0 <= sum)) (PreH33 : (sum <= (200000 * 1000000000 ))) (PreH34 : (0 <= closest)) (PreH35 : (closest <= 1000000000)) (PreH36 : ((Zlength (parent)) = n_pre)) (PreH37 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH38 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH39 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH40 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH41 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH42 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH43 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH44 : (DSUState n_pre roads selected parent )) (PreH45 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parent 0)) /\ ((Znth i parent 0) < n_pre))) ”
).

Definition solver_partial_solve_wit_5_pure_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : (closest <= INT64_MAX)) (PreH3 : (sum <= INT64_MAX)) (PreH4 : (k_pre <= INT64_MAX)) (PreH5 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH6 : (closest >= INT64_MIN)) (PreH7 : (sum >= INT64_MIN)) (PreH8 : (k_pre >= INT64_MIN)) (PreH9 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH10 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH11 : (used <= INT_MAX)) (PreH12 : (i_2 <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH16 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH17 : (used >= INT_MIN)) (PreH18 : (i_2 >= INT_MIN)) (PreH19 : (m_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : (2 <= n_pre)) (PreH22 : (n_pre <= 200000)) (PreH23 : (1 <= k_pre)) (PreH24 : (k_pre <= 1000000000)) (PreH25 : (Pre n_pre k_pre roads )) (PreH26 : (m_pre = (Zlength (roads)))) (PreH27 : ((n_pre - 1 ) <= m_pre)) (PreH28 : (0 <= i_2)) (PreH29 : (i_2 < m_pre)) (PreH30 : (0 <= used)) (PreH31 : (used < (n_pre - 1 ))) (PreH32 : (0 <= sum)) (PreH33 : (sum <= (200000 * 1000000000 ))) (PreH34 : (0 <= closest)) (PreH35 : (closest <= 1000000000)) (PreH36 : ((Zlength (parent)) = n_pre)) (PreH37 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH38 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH39 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH40 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH41 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH42 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH43 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH44 : (DSUState n_pre roads selected parent )) (PreH45 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parent 0)) /\ ((Znth i parent 0) < n_pre))) ”
.

Definition solver_partial_solve_wit_5_aux := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 1000000000)) (PreH5 : (Pre n_pre k_pre roads )) (PreH6 : (m_pre = (Zlength (roads)))) (PreH7 : ((n_pre - 1 ) <= m_pre)) (PreH8 : (0 <= i_2)) (PreH9 : (i_2 < m_pre)) (PreH10 : (0 <= used)) (PreH11 : (used < (n_pre - 1 ))) (PreH12 : (0 <= sum)) (PreH13 : (sum <= (200000 * 1000000000 ))) (PreH14 : (0 <= closest)) (PreH15 : (closest <= 1000000000)) (PreH16 : ((Zlength (parent)) = n_pre)) (PreH17 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH18 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH19 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH20 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH21 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH22 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH23 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH24 : (DSUState n_pre roads selected parent )) (PreH25 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  (IntArray.full p n_pre parent )
|--
  “ (0 <= ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 )) ” 
  &&  “ (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) < n_pre) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parent 0)) /\ ((Znth i parent 0) < n_pre))) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < m_pre) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used < (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum ) ”
  &&  (IntArray.full p n_pre parent )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
.

Definition solver_partial_solve_wit_5 := solver_partial_solve_wit_5_pure -> solver_partial_solve_wit_5_aux.

Definition solver_partial_solve_wit_6_pure := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (0 <= retval)) (PreH2 : (retval < n_pre)) (PreH3 : ((Zlength (parents_after)) = n_pre)) (PreH4 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 parents_after 0)) /\ ((Znth i_3 parents_after 0) < n_pre)))) (PreH5 : (DSURootsPreserved parent parents_after )) (PreH6 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (Pre n_pre k_pre roads )) (PreH12 : (m_pre = (Zlength (roads)))) (PreH13 : ((n_pre - 1 ) <= m_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 < m_pre)) (PreH16 : (0 <= used)) (PreH17 : (used < (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH24 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH25 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH26 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH27 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH28 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH29 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH30 : (DSUState n_pre roads selected parent )) (PreH31 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full p n_pre parents_after )
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ (0 <= ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 )) ” 
  &&  “ (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) < n_pre) ” 
  &&  “ ((Zlength (parents_after)) = n_pre) ” 
  &&  “ (DSUState n_pre roads selected parents_after ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after 0)) /\ ((Znth i parents_after 0) < n_pre))) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : (closest <= INT64_MAX)) (PreH3 : (sum <= INT64_MAX)) (PreH4 : (k_pre <= INT64_MAX)) (PreH5 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH6 : (closest >= INT64_MIN)) (PreH7 : (sum >= INT64_MIN)) (PreH8 : (k_pre >= INT64_MIN)) (PreH9 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH10 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH11 : (used <= INT_MAX)) (PreH12 : (i_2 <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (retval <= INT_MAX)) (PreH16 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH17 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH18 : (used >= INT_MIN)) (PreH19 : (i_2 >= INT_MIN)) (PreH20 : (m_pre >= INT_MIN)) (PreH21 : (n_pre >= INT_MIN)) (PreH22 : (retval >= INT_MIN)) (PreH23 : (0 <= retval)) (PreH24 : (retval < n_pre)) (PreH25 : ((Zlength (parents_after)) = n_pre)) (PreH26 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 parents_after 0)) /\ ((Znth i_3 parents_after 0) < n_pre)))) (PreH27 : (DSURootsPreserved parent parents_after )) (PreH28 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH29 : (2 <= n_pre)) (PreH30 : (n_pre <= 200000)) (PreH31 : (1 <= k_pre)) (PreH32 : (k_pre <= 1000000000)) (PreH33 : (Pre n_pre k_pre roads )) (PreH34 : (m_pre = (Zlength (roads)))) (PreH35 : ((n_pre - 1 ) <= m_pre)) (PreH36 : (0 <= i_2)) (PreH37 : (i_2 < m_pre)) (PreH38 : (0 <= used)) (PreH39 : (used < (n_pre - 1 ))) (PreH40 : (0 <= sum)) (PreH41 : (sum <= (200000 * 1000000000 ))) (PreH42 : (0 <= closest)) (PreH43 : (closest <= 1000000000)) (PreH44 : ((Zlength (parent)) = n_pre)) (PreH45 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH46 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH47 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH48 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH49 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH50 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH51 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH52 : (DSUState n_pre roads selected parent )) (PreH53 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full p n_pre parents_after )
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after 0)) /\ ((Znth i parents_after 0) < n_pre))) ” 
  &&  “ (DSUState n_pre roads selected parents_after ) ”
).

Definition solver_partial_solve_wit_6_pure_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : (closest <= INT64_MAX)) (PreH3 : (sum <= INT64_MAX)) (PreH4 : (k_pre <= INT64_MAX)) (PreH5 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH6 : (closest >= INT64_MIN)) (PreH7 : (sum >= INT64_MIN)) (PreH8 : (k_pre >= INT64_MIN)) (PreH9 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH10 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH11 : (used <= INT_MAX)) (PreH12 : (i_2 <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (retval <= INT_MAX)) (PreH16 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH17 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH18 : (used >= INT_MIN)) (PreH19 : (i_2 >= INT_MIN)) (PreH20 : (m_pre >= INT_MIN)) (PreH21 : (n_pre >= INT_MIN)) (PreH22 : (retval >= INT_MIN)) (PreH23 : (0 <= retval)) (PreH24 : (retval < n_pre)) (PreH25 : ((Zlength (parents_after)) = n_pre)) (PreH26 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 parents_after 0)) /\ ((Znth i_3 parents_after 0) < n_pre)))) (PreH27 : (DSURootsPreserved parent parents_after )) (PreH28 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH29 : (2 <= n_pre)) (PreH30 : (n_pre <= 200000)) (PreH31 : (1 <= k_pre)) (PreH32 : (k_pre <= 1000000000)) (PreH33 : (Pre n_pre k_pre roads )) (PreH34 : (m_pre = (Zlength (roads)))) (PreH35 : ((n_pre - 1 ) <= m_pre)) (PreH36 : (0 <= i_2)) (PreH37 : (i_2 < m_pre)) (PreH38 : (0 <= used)) (PreH39 : (used < (n_pre - 1 ))) (PreH40 : (0 <= sum)) (PreH41 : (sum <= (200000 * 1000000000 ))) (PreH42 : (0 <= closest)) (PreH43 : (closest <= 1000000000)) (PreH44 : ((Zlength (parent)) = n_pre)) (PreH45 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH46 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH47 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH48 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH49 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH50 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH51 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH52 : (DSUState n_pre roads selected parent )) (PreH53 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full p n_pre parents_after )
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after 0)) /\ ((Znth i parents_after 0) < n_pre))) ”
.

Definition solver_partial_solve_wit_6_pure_split_goal_2 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= INT64_MAX)) (PreH2 : (closest <= INT64_MAX)) (PreH3 : (sum <= INT64_MAX)) (PreH4 : (k_pre <= INT64_MAX)) (PreH5 : ((ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) >= INT64_MIN)) (PreH6 : (closest >= INT64_MIN)) (PreH7 : (sum >= INT64_MIN)) (PreH8 : (k_pre >= INT64_MIN)) (PreH9 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH10 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) <= INT_MAX)) (PreH11 : (used <= INT_MAX)) (PreH12 : (i_2 <= INT_MAX)) (PreH13 : (m_pre <= INT_MAX)) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (retval <= INT_MAX)) (PreH16 : (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH17 : (((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) >= INT_MIN)) (PreH18 : (used >= INT_MIN)) (PreH19 : (i_2 >= INT_MIN)) (PreH20 : (m_pre >= INT_MIN)) (PreH21 : (n_pre >= INT_MIN)) (PreH22 : (retval >= INT_MIN)) (PreH23 : (0 <= retval)) (PreH24 : (retval < n_pre)) (PreH25 : ((Zlength (parents_after)) = n_pre)) (PreH26 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 parents_after 0)) /\ ((Znth i_3 parents_after 0) < n_pre)))) (PreH27 : (DSURootsPreserved parent parents_after )) (PreH28 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH29 : (2 <= n_pre)) (PreH30 : (n_pre <= 200000)) (PreH31 : (1 <= k_pre)) (PreH32 : (k_pre <= 1000000000)) (PreH33 : (Pre n_pre k_pre roads )) (PreH34 : (m_pre = (Zlength (roads)))) (PreH35 : ((n_pre - 1 ) <= m_pre)) (PreH36 : (0 <= i_2)) (PreH37 : (i_2 < m_pre)) (PreH38 : (0 <= used)) (PreH39 : (used < (n_pre - 1 ))) (PreH40 : (0 <= sum)) (PreH41 : (sum <= (200000 * 1000000000 ))) (PreH42 : (0 <= closest)) (PreH43 : (closest <= 1000000000)) (PreH44 : ((Zlength (parent)) = n_pre)) (PreH45 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH46 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH47 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH48 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH49 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH50 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH51 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH52 : (DSUState n_pre roads selected parent )) (PreH53 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full p n_pre parents_after )
  **  ((( &( "a" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
  **  ((( &( "p" ) )) # Ptr  |-> p)
|--
  “ (DSUState n_pre roads selected parents_after ) ”
.

Definition solver_partial_solve_wit_6_aux := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (0 <= retval)) (PreH2 : (retval < n_pre)) (PreH3 : ((Zlength (parents_after)) = n_pre)) (PreH4 : forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 parents_after 0)) /\ ((Znth i_3 parents_after 0) < n_pre)))) (PreH5 : (DSURootsPreserved parent parents_after )) (PreH6 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH7 : (2 <= n_pre)) (PreH8 : (n_pre <= 200000)) (PreH9 : (1 <= k_pre)) (PreH10 : (k_pre <= 1000000000)) (PreH11 : (Pre n_pre k_pre roads )) (PreH12 : (m_pre = (Zlength (roads)))) (PreH13 : ((n_pre - 1 ) <= m_pre)) (PreH14 : (0 <= i_2)) (PreH15 : (i_2 < m_pre)) (PreH16 : (0 <= used)) (PreH17 : (used < (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH24 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH25 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH26 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH27 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH28 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH29 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH30 : (DSUState n_pre roads selected parent )) (PreH31 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  (IntArray.full p n_pre parents_after )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
|--
  “ (0 <= ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 )) ” 
  &&  “ (((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) < n_pre) ” 
  &&  “ ((Zlength (parents_after)) = n_pre) ” 
  &&  “ (DSUState n_pre roads selected parents_after ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after 0)) /\ ((Znth i parents_after 0) < n_pre))) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ ((Zlength (parents_after)) = n_pre) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((0 <= (Znth i_3 parents_after 0)) /\ ((Znth i_3 parents_after 0) < n_pre))) ” 
  &&  “ (DSURootsPreserved parent parents_after ) ” 
  &&  “ (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < m_pre) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used < (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum ) ”
  &&  (IntArray.full p n_pre parents_after )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
.

Definition solver_partial_solve_wit_6 := solver_partial_solve_wit_6_pure -> solver_partial_solve_wit_6_aux.

Definition solver_partial_solve_wit_7 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (i_2: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (parents_after: (@list Z)) (retval: Z) (parents_after_2: (@list Z)) (retval_2: Z)  __default__Prod__Prod_Z_Z_Z (PreH1 : (retval <> retval_2)) (PreH2 : (0 <= retval_2)) (PreH3 : (retval_2 < n_pre)) (PreH4 : ((Zlength (parents_after_2)) = n_pre)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after_2 0)) /\ ((Znth i parents_after_2 0) < n_pre)))) (PreH6 : (DSURootsPreserved parents_after parents_after_2 )) (PreH7 : (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 )) (PreH8 : (0 <= retval)) (PreH9 : (retval < n_pre)) (PreH10 : ((Zlength (parents_after)) = n_pre)) (PreH11 : forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after 0)) /\ ((Znth i parents_after 0) < n_pre)))) (PreH12 : (DSURootsPreserved parent parents_after )) (PreH13 : (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval )) (PreH14 : (2 <= n_pre)) (PreH15 : (n_pre <= 200000)) (PreH16 : (1 <= k_pre)) (PreH17 : (k_pre <= 1000000000)) (PreH18 : (Pre n_pre k_pre roads )) (PreH19 : (m_pre = (Zlength (roads)))) (PreH20 : ((n_pre - 1 ) <= m_pre)) (PreH21 : (0 <= i_2)) (PreH22 : (i_2 < m_pre)) (PreH23 : (0 <= used)) (PreH24 : (used < (n_pre - 1 ))) (PreH25 : (0 <= sum)) (PreH26 : (sum <= (200000 * 1000000000 ))) (PreH27 : (0 <= closest)) (PreH28 : (closest <= 1000000000)) (PreH29 : ((Zlength (parent)) = n_pre)) (PreH30 : forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre)))) (PreH31 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH32 : (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH33 : ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH34 : (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))) (PreH35 : ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre)) (PreH36 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH37 : (DSUState n_pre roads selected parent )) (PreH38 : (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum )) ,
  (IntArray.full p n_pre parents_after_2 )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
|--
  “ (retval <> retval_2) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < n_pre) ” 
  &&  “ ((Zlength (parents_after_2)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after_2 0)) /\ ((Znth i parents_after_2 0) < n_pre))) ” 
  &&  “ (DSURootsPreserved parents_after parents_after_2 ) ” 
  &&  “ (DSUFindResult n_pre roads selected parents_after parents_after_2 ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval_2 ) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < n_pre) ” 
  &&  “ ((Zlength (parents_after)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((0 <= (Znth i parents_after 0)) /\ ((Znth i parents_after 0) < n_pre))) ” 
  &&  “ (DSURootsPreserved parent parents_after ) ” 
  &&  “ (DSUFindResult n_pre roads selected parent parents_after ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ) retval ) ” 
  &&  “ (2 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= 1000000000) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ ((n_pre - 1 ) <= m_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 < m_pre) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used < (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((0 <= (Znth j parent 0)) /\ ((Znth j parent 0) < n_pre))) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (1 <= (ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (1 <= (ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z)))) ” 
  &&  “ ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) <= n_pre) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order i_2 selected used sum ) ”
  &&  (((p + (retval * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i p retval 0 n_pre parents_after_2 )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.missing_i e i_2 0 m_pre sorted_roads )
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "u")) # Int  |-> ((ztriple_1 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "v")) # Int  |-> ((ztriple_2 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))) - 1 ))
  **  ((&(((e + (i_2 * sizeof( "<anonymous struct>" ))))  # "anonymous struct 1" ->ₛ "w")) # Int64  |-> (ztriple_3 ((Znth i_2 sorted_roads __default__Prod__Prod_Z_Z_Z))))
.

Definition solver_partial_solve_wit_8_pure := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (Pre n_pre k_pre roads )) (PreH3 : (0 <= processed)) (PreH4 : (processed <= m_pre)) (PreH5 : (used = (n_pre - 1 ))) (PreH6 : (0 <= sum)) (PreH7 : (sum <= (200000 * 1000000000 ))) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : ((Zlength (parent)) = n_pre)) (PreH11 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH12 : (RoadEncoding sorted_roads sorted_raw )) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (DSUState n_pre roads selected parent )) (PreH15 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH16 : (sum <> 0)) (PreH17 : (Spec n_pre k_pre roads sum )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre )
|--
  “ (0 <= m_pre) ” 
  &&  “ ((Zlength (sorted_roads)) = m_pre) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (sum <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (closest >= INT64_MIN)) (PreH5 : (sum >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (used <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (used >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (m_pre = (Zlength (roads)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (0 <= processed)) (PreH16 : (processed <= m_pre)) (PreH17 : (used = (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH24 : (RoadEncoding sorted_roads sorted_raw )) (PreH25 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH26 : (DSUState n_pre roads selected parent )) (PreH27 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH28 : (sum <> 0)) (PreH29 : (Spec n_pre k_pre roads sum )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ ((Zlength (sorted_roads)) = m_pre) ”
).

Definition solver_partial_solve_wit_8_pure_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (sum <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (closest >= INT64_MIN)) (PreH5 : (sum >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (used <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (used >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (m_pre = (Zlength (roads)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (0 <= processed)) (PreH16 : (processed <= m_pre)) (PreH17 : (used = (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH24 : (RoadEncoding sorted_roads sorted_raw )) (PreH25 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH26 : (DSUState n_pre roads selected parent )) (PreH27 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH28 : (sum <> 0)) (PreH29 : (Spec n_pre k_pre roads sum )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ ((Zlength (sorted_roads)) = m_pre) ”
.

Definition solver_partial_solve_wit_8_aux := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (Pre n_pre k_pre roads )) (PreH3 : (0 <= processed)) (PreH4 : (processed <= m_pre)) (PreH5 : (used = (n_pre - 1 ))) (PreH6 : (0 <= sum)) (PreH7 : (sum <= (200000 * 1000000000 ))) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : ((Zlength (parent)) = n_pre)) (PreH11 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH12 : (RoadEncoding sorted_roads sorted_raw )) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (DSUState n_pre roads selected parent )) (PreH15 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH16 : (sum <> 0)) (PreH17 : (Spec n_pre k_pre roads sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre )
|--
  “ (0 <= m_pre) ” 
  &&  “ ((Zlength (sorted_roads)) = m_pre) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= processed) ” 
  &&  “ (processed <= m_pre) ” 
  &&  “ (used = (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (RoadEncoding sorted_roads sorted_raw ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum ) ” 
  &&  “ (sum <> 0) ” 
  &&  “ (Spec n_pre k_pre roads sum ) ”
  &&  (EdgeArray.full e m_pre sorted_roads )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (IntArray.full p n_pre parent )
.

Definition solver_partial_solve_wit_8 := solver_partial_solve_wit_8_pure -> solver_partial_solve_wit_8_aux.

Definition solver_partial_solve_wit_9_pure := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (Pre n_pre k_pre roads )) (PreH3 : (0 <= processed)) (PreH4 : (processed <= m_pre)) (PreH5 : (used = (n_pre - 1 ))) (PreH6 : (0 <= sum)) (PreH7 : (sum <= (200000 * 1000000000 ))) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : ((Zlength (parent)) = n_pre)) (PreH11 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH12 : (RoadEncoding sorted_roads sorted_raw )) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (DSUState n_pre roads selected parent )) (PreH15 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH16 : (sum = 0)) (PreH17 : (Spec n_pre k_pre roads closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre )
|--
  “ (0 <= m_pre) ” 
  &&  “ ((Zlength (sorted_roads)) = m_pre) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (sum <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (closest >= INT64_MIN)) (PreH5 : (sum >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (used <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (used >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (m_pre = (Zlength (roads)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (0 <= processed)) (PreH16 : (processed <= m_pre)) (PreH17 : (used = (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH24 : (RoadEncoding sorted_roads sorted_raw )) (PreH25 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH26 : (DSUState n_pre roads selected parent )) (PreH27 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH28 : (sum = 0)) (PreH29 : (Spec n_pre k_pre roads closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ ((Zlength (sorted_roads)) = m_pre) ”
).

Definition solver_partial_solve_wit_9_pure_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (sum <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (closest >= INT64_MIN)) (PreH5 : (sum >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (used <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (used >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (m_pre = (Zlength (roads)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (0 <= processed)) (PreH16 : (processed <= m_pre)) (PreH17 : (used = (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH24 : (RoadEncoding sorted_roads sorted_raw )) (PreH25 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH26 : (DSUState n_pre roads selected parent )) (PreH27 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH28 : (sum = 0)) (PreH29 : (Spec n_pre k_pre roads closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  (EdgeArray.full e m_pre sorted_roads )
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ ((Zlength (sorted_roads)) = m_pre) ”
.

Definition solver_partial_solve_wit_9_aux := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (Pre n_pre k_pre roads )) (PreH3 : (0 <= processed)) (PreH4 : (processed <= m_pre)) (PreH5 : (used = (n_pre - 1 ))) (PreH6 : (0 <= sum)) (PreH7 : (sum <= (200000 * 1000000000 ))) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : ((Zlength (parent)) = n_pre)) (PreH11 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH12 : (RoadEncoding sorted_roads sorted_raw )) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (DSUState n_pre roads selected parent )) (PreH15 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH16 : (sum = 0)) (PreH17 : (Spec n_pre k_pre roads closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (EdgeArray.full e m_pre sorted_roads )
  **  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre )
|--
  “ (0 <= m_pre) ” 
  &&  “ ((Zlength (sorted_roads)) = m_pre) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= processed) ” 
  &&  “ (processed <= m_pre) ” 
  &&  “ (used = (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (RoadEncoding sorted_roads sorted_raw ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum ) ” 
  &&  “ (sum = 0) ” 
  &&  “ (Spec n_pre k_pre roads closest ) ”
  &&  (EdgeArray.full e m_pre sorted_roads )
  **  (EdgeArray.full input_pre m_pre roads )
  **  (IntArray.full p n_pre parent )
.

Definition solver_partial_solve_wit_9 := solver_partial_solve_wit_9_pure -> solver_partial_solve_wit_9_aux.

Definition solver_partial_solve_wit_10_pure := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (Pre n_pre k_pre roads )) (PreH3 : (0 <= processed)) (PreH4 : (processed <= m_pre)) (PreH5 : (used = (n_pre - 1 ))) (PreH6 : (0 <= sum)) (PreH7 : (sum <= (200000 * 1000000000 ))) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : ((Zlength (parent)) = n_pre)) (PreH11 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH12 : (RoadEncoding sorted_roads sorted_raw )) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (DSUState n_pre roads selected parent )) (PreH15 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH16 : (sum <> 0)) (PreH17 : (Spec n_pre k_pre roads sum )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ (n_pre <= n_pre) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (sum <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (closest >= INT64_MIN)) (PreH5 : (sum >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (used <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (used >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (m_pre = (Zlength (roads)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (0 <= processed)) (PreH16 : (processed <= m_pre)) (PreH17 : (used = (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH24 : (RoadEncoding sorted_roads sorted_raw )) (PreH25 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH26 : (DSUState n_pre roads selected parent )) (PreH27 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH28 : (sum <> 0)) (PreH29 : (Spec n_pre k_pre roads sum )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ (0 <= n_pre) ”
).

Definition solver_partial_solve_wit_10_pure_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (sum <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (closest >= INT64_MIN)) (PreH5 : (sum >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (used <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (used >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (m_pre = (Zlength (roads)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (0 <= processed)) (PreH16 : (processed <= m_pre)) (PreH17 : (used = (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH24 : (RoadEncoding sorted_roads sorted_raw )) (PreH25 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH26 : (DSUState n_pre roads selected parent )) (PreH27 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH28 : (sum <> 0)) (PreH29 : (Spec n_pre k_pre roads sum )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ (0 <= n_pre) ”
.

Definition solver_partial_solve_wit_10_aux := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (Pre n_pre k_pre roads )) (PreH3 : (0 <= processed)) (PreH4 : (processed <= m_pre)) (PreH5 : (used = (n_pre - 1 ))) (PreH6 : (0 <= sum)) (PreH7 : (sum <= (200000 * 1000000000 ))) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : ((Zlength (parent)) = n_pre)) (PreH11 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH12 : (RoadEncoding sorted_roads sorted_raw )) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (DSUState n_pre roads selected parent )) (PreH15 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH16 : (sum <> 0)) (PreH17 : (Spec n_pre k_pre roads sum )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (IntArray.full p n_pre parent )
|--
  “ (n_pre <= n_pre) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= processed) ” 
  &&  “ (processed <= m_pre) ” 
  &&  “ (used = (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (RoadEncoding sorted_roads sorted_raw ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum ) ” 
  &&  “ (sum <> 0) ” 
  &&  “ (Spec n_pre k_pre roads sum ) ”
  &&  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre )
  **  (EdgeArray.full input_pre m_pre roads )
.

Definition solver_partial_solve_wit_10 := solver_partial_solve_wit_10_pure -> solver_partial_solve_wit_10_aux.

Definition solver_partial_solve_wit_11_pure := 
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (Pre n_pre k_pre roads )) (PreH3 : (0 <= processed)) (PreH4 : (processed <= m_pre)) (PreH5 : (used = (n_pre - 1 ))) (PreH6 : (0 <= sum)) (PreH7 : (sum <= (200000 * 1000000000 ))) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : ((Zlength (parent)) = n_pre)) (PreH11 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH12 : (RoadEncoding sorted_roads sorted_raw )) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (DSUState n_pre roads selected parent )) (PreH15 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH16 : (sum = 0)) (PreH17 : (Spec n_pre k_pre roads closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ (n_pre <= n_pre) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (0 <= n_pre) ”
) \/
(
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (sum <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (closest >= INT64_MIN)) (PreH5 : (sum >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (used <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (used >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (m_pre = (Zlength (roads)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (0 <= processed)) (PreH16 : (processed <= m_pre)) (PreH17 : (used = (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH24 : (RoadEncoding sorted_roads sorted_raw )) (PreH25 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH26 : (DSUState n_pre roads selected parent )) (PreH27 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH28 : (sum = 0)) (PreH29 : (Spec n_pre k_pre roads closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ (0 <= n_pre) ”
).

Definition solver_partial_solve_wit_11_pure_split_goal_1 := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (e: Z) (p: Z) (PreH1 : (closest <= INT64_MAX)) (PreH2 : (sum <= INT64_MAX)) (PreH3 : (k_pre <= INT64_MAX)) (PreH4 : (closest >= INT64_MIN)) (PreH5 : (sum >= INT64_MIN)) (PreH6 : (k_pre >= INT64_MIN)) (PreH7 : (used <= INT_MAX)) (PreH8 : (m_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (used >= INT_MIN)) (PreH11 : (m_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (m_pre = (Zlength (roads)))) (PreH14 : (Pre n_pre k_pre roads )) (PreH15 : (0 <= processed)) (PreH16 : (processed <= m_pre)) (PreH17 : (used = (n_pre - 1 ))) (PreH18 : (0 <= sum)) (PreH19 : (sum <= (200000 * 1000000000 ))) (PreH20 : (0 <= closest)) (PreH21 : (closest <= 1000000000)) (PreH22 : ((Zlength (parent)) = n_pre)) (PreH23 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH24 : (RoadEncoding sorted_roads sorted_raw )) (PreH25 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH26 : (DSUState n_pre roads selected parent )) (PreH27 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH28 : (sum = 0)) (PreH29 : (Spec n_pre k_pre roads closest )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "k" ) )) # Int64  |-> k_pre)
  **  ((( &( "input" ) )) # Ptr  |-> input_pre)
  **  ((( &( "used" ) )) # Int  |-> used)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  ((( &( "closest" ) )) # Int64  |-> closest)
  **  (EdgeArray.full input_pre m_pre roads )
  **  ((( &( "e" ) )) # Ptr  |-> e)
  **  ((( &( "p" ) )) # Ptr  |-> p)
  **  (IntArray.full p n_pre parent )
|--
  “ (0 <= n_pre) ”
.

Definition solver_partial_solve_wit_11_aux := 
forall (input_pre: Z) (k_pre: Z) (m_pre: Z) (n_pre: Z) (roads: (@list ((Z * Z) * Z))) (sorted_roads: (@list ((Z * Z) * Z))) (sorted_raw: (@list Z)) (order: (@list Z)) (parent: (@list Z)) (selected: (@list Z)) (processed: Z) (used: Z) (sum: Z) (closest: Z) (p: Z) (PreH1 : (m_pre = (Zlength (roads)))) (PreH2 : (Pre n_pre k_pre roads )) (PreH3 : (0 <= processed)) (PreH4 : (processed <= m_pre)) (PreH5 : (used = (n_pre - 1 ))) (PreH6 : (0 <= sum)) (PreH7 : (sum <= (200000 * 1000000000 ))) (PreH8 : (0 <= closest)) (PreH9 : (closest <= 1000000000)) (PreH10 : ((Zlength (parent)) = n_pre)) (PreH11 : (RoadSortResult roads sorted_roads sorted_raw order )) (PreH12 : (RoadEncoding sorted_roads sorted_raw )) (PreH13 : (ClosestRoadPrefix k_pre roads m_pre closest )) (PreH14 : (DSUState n_pre roads selected parent )) (PreH15 : (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum )) (PreH16 : (sum = 0)) (PreH17 : (Spec n_pre k_pre roads closest )) ,
  (EdgeArray.full input_pre m_pre roads )
  **  (IntArray.full p n_pre parent )
|--
  “ (n_pre <= n_pre) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (m_pre = (Zlength (roads))) ” 
  &&  “ (Pre n_pre k_pre roads ) ” 
  &&  “ (0 <= processed) ” 
  &&  “ (processed <= m_pre) ” 
  &&  “ (used = (n_pre - 1 )) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (200000 * 1000000000 )) ” 
  &&  “ (0 <= closest) ” 
  &&  “ (closest <= 1000000000) ” 
  &&  “ ((Zlength (parent)) = n_pre) ” 
  &&  “ (RoadSortResult roads sorted_roads sorted_raw order ) ” 
  &&  “ (RoadEncoding sorted_roads sorted_raw ) ” 
  &&  “ (ClosestRoadPrefix k_pre roads m_pre closest ) ” 
  &&  “ (DSUState n_pre roads selected parent ) ” 
  &&  “ (KruskalPrefixState n_pre k_pre roads sorted_roads order processed selected used sum ) ” 
  &&  “ (sum = 0) ” 
  &&  “ (Spec n_pre k_pre roads closest ) ”
  &&  (IntArray.full p n_pre parent )
  **  (IntArray.undef_seg p n_pre n_pre )
  **  (EdgeArray.full input_pre m_pre roads )
.

Definition solver_partial_solve_wit_11 := solver_partial_solve_wit_11_pure -> solver_partial_solve_wit_11_aux.

Module Type VC_Correct.


Axiom proof_of_cmp_edge_safety_wit_1 : cmp_edge_safety_wit_1.
Axiom proof_of_cmp_edge_safety_wit_2 : cmp_edge_safety_wit_2.
Axiom proof_of_cmp_edge_safety_wit_3 : cmp_edge_safety_wit_3.
Axiom proof_of_cmp_edge_safety_wit_4 : cmp_edge_safety_wit_4.
Axiom proof_of_cmp_edge_entail_wit_1 : cmp_edge_entail_wit_1.
Axiom proof_of_cmp_edge_return_wit_1 : cmp_edge_return_wit_1.
Axiom proof_of_cmp_edge_return_wit_2 : cmp_edge_return_wit_2.
Axiom proof_of_cmp_edge_return_wit_3 : cmp_edge_return_wit_3.
Axiom proof_of_find_entail_wit_1 : find_entail_wit_1.
Axiom proof_of_find_entail_wit_2 : find_entail_wit_2.
Axiom proof_of_find_return_wit_1 : find_return_wit_1.
Axiom proof_of_find_partial_solve_wit_1 : find_partial_solve_wit_1.
Axiom proof_of_find_partial_solve_wit_2 : find_partial_solve_wit_2.
Axiom proof_of_find_partial_solve_wit_3 : find_partial_solve_wit_3.
Axiom proof_of_find_partial_solve_wit_4 : find_partial_solve_wit_4.
Axiom proof_of_find_partial_solve_wit_5 : find_partial_solve_wit_5.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Axiom proof_of_solver_entail_wit_3_4 : solver_entail_wit_3_4.
Axiom proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Axiom proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Axiom proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Axiom proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Axiom proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Axiom proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Axiom proof_of_solver_entail_wit_10_3 : solver_entail_wit_10_3.
Axiom proof_of_solver_entail_wit_11_1 : solver_entail_wit_11_1.
Axiom proof_of_solver_entail_wit_11_2 : solver_entail_wit_11_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2_pure : solver_partial_solve_wit_2_pure.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8_pure : solver_partial_solve_wit_8_pure.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9_pure : solver_partial_solve_wit_9_pure.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10_pure : solver_partial_solve_wit_10_pure.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11_pure : solver_partial_solve_wit_11_pure.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.

End VC_Correct.
