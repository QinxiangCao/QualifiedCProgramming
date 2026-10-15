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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P029_817A_treasure_hunt_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre >= x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |->_)
  **  ((( &( "dx" ) )) # Int64  |->_)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ ((x1_pre - x2_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (x1_pre - x2_pre )) ”
.

Definition solver_safety_wit_2 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre < x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |->_)
  **  ((( &( "dx" ) )) # Int64  |->_)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ ((x2_pre - x1_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (x2_pre - x1_pre )) ”
.

Definition solver_safety_wit_3 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre >= y2_pre)) (PreH2 : ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "dy" ) )) # Int64  |->_)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ ((y1_pre - y2_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (y1_pre - y2_pre )) ”
.

Definition solver_safety_wit_4 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre < y2_pre)) (PreH2 : ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "dy" ) )) # Int64  |->_)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ ((y2_pre - y1_pre ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (y2_pre - y1_pre )) ”
.

Definition solver_safety_wit_5 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (((AbsDiff (x1_pre) (x2_pre)) <> (INT64_MIN)) \/ (x_pre <> (-1))) ” 
  &&  “ (x_pre <> 0) ”
.

Definition solver_safety_wit_6 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH2 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (((AbsDiff (y1_pre) (y2_pre)) <> (INT64_MIN)) \/ (y_pre <> (-1))) ” 
  &&  “ (y_pre <> 0) ”
.

Definition solver_safety_wit_8 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH2 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_9 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) <> 0)) (PreH2 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_10 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) <> 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_11 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ ((((AbsDiff (y1_pre) (y2_pre)) ÷ y_pre ) <> (INT64_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_12 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (((AbsDiff (y1_pre) (y2_pre)) <> (INT64_MIN)) \/ (y_pre <> (-1))) ” 
  &&  “ (y_pre <> 0) ”
.

Definition solver_safety_wit_13 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ ((((AbsDiff (x1_pre) (x2_pre)) ÷ x_pre ) <> (INT64_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition solver_safety_wit_14 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (((AbsDiff (x1_pre) (x2_pre)) <> (INT64_MIN)) \/ (x_pre <> (-1))) ” 
  &&  “ (x_pre <> 0) ”
.

Definition solver_safety_wit_15 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_16 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
  **  ((( &( "y2" ) )) # Int64  |-> y2_pre)
  **  ((( &( "y1" ) )) # Int64  |-> y1_pre)
  **  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
  **  ((( &( "x2" ) )) # Int64  |-> x2_pre)
  **  ((( &( "x1" ) )) # Int64  |-> x1_pre)
  **  ((( &( "x" ) )) # Int64  |-> x_pre)
  **  ((( &( "y" ) )) # Int64  |-> y_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_entail_wit_1_1 := 
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre >= x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dx" ) )) # Int64  |-> (x1_pre - x2_pre ))
|--
  “ ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre))) ” 
  &&  “ ((-100000) <= x1_pre) ” 
  &&  “ (x1_pre <= 100000) ” 
  &&  “ ((-100000) <= y1_pre) ” 
  &&  “ (y1_pre <= 100000) ” 
  &&  “ ((-100000) <= x2_pre) ” 
  &&  “ (x2_pre <= 100000) ” 
  &&  “ ((-100000) <= y2_pre) ” 
  &&  “ (y2_pre <= 100000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 100000) ” 
  &&  “ (1 <= y_pre) ” 
  &&  “ (y_pre <= 100000) ”
  &&  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
) \/
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre >= x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ ((x1_pre - x2_pre ) = (AbsDiff (x1_pre) (x2_pre))) ”
  &&  emp
).

Definition solver_entail_wit_1_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre >= x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((x1_pre - x2_pre ) = (AbsDiff (x1_pre) (x2_pre)))
.

Definition solver_entail_wit_1_2 := 
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre < x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((( &( "dx" ) )) # Int64  |-> (x2_pre - x1_pre ))
|--
  “ ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre))) ” 
  &&  “ ((-100000) <= x1_pre) ” 
  &&  “ (x1_pre <= 100000) ” 
  &&  “ ((-100000) <= y1_pre) ” 
  &&  “ (y1_pre <= 100000) ” 
  &&  “ ((-100000) <= x2_pre) ” 
  &&  “ (x2_pre <= 100000) ” 
  &&  “ ((-100000) <= y2_pre) ” 
  &&  “ (y2_pre <= 100000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 100000) ” 
  &&  “ (1 <= y_pre) ” 
  &&  “ (y_pre <= 100000) ”
  &&  ((( &( "dx" ) )) # Int64  |-> (AbsDiff (x1_pre) (x2_pre)))
) \/
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre < x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ ((x2_pre - x1_pre ) = (AbsDiff (x1_pre) (x2_pre))) ”
  &&  emp
).

Definition solver_entail_wit_1_2_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (x1_pre < x2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((x2_pre - x1_pre ) = (AbsDiff (x1_pre) (x2_pre)))
.

Definition solver_entail_wit_2_1 := 
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre >= y2_pre)) (PreH2 : ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (y1_pre - y2_pre ))
|--
  “ ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre))) ” 
  &&  “ ((-100000) <= x1_pre) ” 
  &&  “ (x1_pre <= 100000) ” 
  &&  “ ((-100000) <= y1_pre) ” 
  &&  “ (y1_pre <= 100000) ” 
  &&  “ ((-100000) <= x2_pre) ” 
  &&  “ (x2_pre <= 100000) ” 
  &&  “ ((-100000) <= y2_pre) ” 
  &&  “ (y2_pre <= 100000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 100000) ” 
  &&  “ (1 <= y_pre) ” 
  &&  “ (y_pre <= 100000) ”
  &&  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
) \/
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre >= y2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ ((y1_pre - y2_pre ) = (AbsDiff (y1_pre) (y2_pre))) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre >= y2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((y1_pre - y2_pre ) = (AbsDiff (y1_pre) (y2_pre)))
.

Definition solver_entail_wit_2_2 := 
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre < y2_pre)) (PreH2 : ((AbsDiff (x1_pre) (x2_pre)) = (AbsDiff (x1_pre) (x2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  ((( &( "dy" ) )) # Int64  |-> (y2_pre - y1_pre ))
|--
  “ ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre))) ” 
  &&  “ ((-100000) <= x1_pre) ” 
  &&  “ (x1_pre <= 100000) ” 
  &&  “ ((-100000) <= y1_pre) ” 
  &&  “ (y1_pre <= 100000) ” 
  &&  “ ((-100000) <= x2_pre) ” 
  &&  “ (x2_pre <= 100000) ” 
  &&  “ ((-100000) <= y2_pre) ” 
  &&  “ (y2_pre <= 100000) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= 100000) ” 
  &&  “ (1 <= y_pre) ” 
  &&  “ (y_pre <= 100000) ”
  &&  ((( &( "dy" ) )) # Int64  |-> (AbsDiff (y1_pre) (y2_pre)))
) \/
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre < y2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ ((y2_pre - y1_pre ) = (AbsDiff (y1_pre) (y2_pre))) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (y1_pre < y2_pre)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  ((y2_pre - y1_pre ) = (AbsDiff (y1_pre) (y2_pre)))
.

Definition solver_return_wit_1 := 
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : ((((AbsDiff (x1_pre) (x2_pre)) ÷ x_pre ) % ( 2 ) ) <> (((AbsDiff (y1_pre) (y2_pre)) ÷ y_pre ) % ( 2 ) ))) (PreH2 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH3 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH4 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH5 : ((-100000) <= x1_pre)) (PreH6 : (x1_pre <= 100000)) (PreH7 : ((-100000) <= y1_pre)) (PreH8 : (y1_pre <= 100000)) (PreH9 : ((-100000) <= x2_pre)) (PreH10 : (x2_pre <= 100000)) (PreH11 : ((-100000) <= y2_pre)) (PreH12 : (y2_pre <= 100000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre <= 100000)) (PreH15 : (1 <= y_pre)) (PreH16 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 0 ) ”
  &&  emp
) \/
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : ((((AbsDiff (x1_pre) (x2_pre)) ÷ x_pre ) % ( 2 ) ) <> (((AbsDiff (y1_pre) (y2_pre)) ÷ y_pre ) % ( 2 ) ))) (PreH2 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH3 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 0 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : ((((AbsDiff (x1_pre) (x2_pre)) ÷ x_pre ) % ( 2 ) ) <> (((AbsDiff (y1_pre) (y2_pre)) ÷ y_pre ) % ( 2 ) ))) (PreH2 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH3 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 0 )
.

Definition solver_return_wit_2 := 
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : ((((AbsDiff (x1_pre) (x2_pre)) ÷ x_pre ) % ( 2 ) ) = (((AbsDiff (y1_pre) (y2_pre)) ÷ y_pre ) % ( 2 ) ))) (PreH2 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH3 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH4 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH5 : ((-100000) <= x1_pre)) (PreH6 : (x1_pre <= 100000)) (PreH7 : ((-100000) <= y1_pre)) (PreH8 : (y1_pre <= 100000)) (PreH9 : ((-100000) <= x2_pre)) (PreH10 : (x2_pre <= 100000)) (PreH11 : ((-100000) <= y2_pre)) (PreH12 : (y2_pre <= 100000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre <= 100000)) (PreH15 : (1 <= y_pre)) (PreH16 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 1 ) ”
  &&  emp
) \/
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : ((((AbsDiff (x1_pre) (x2_pre)) ÷ x_pre ) % ( 2 ) ) = (((AbsDiff (y1_pre) (y2_pre)) ÷ y_pre ) % ( 2 ) ))) (PreH2 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH3 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 1 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : ((((AbsDiff (x1_pre) (x2_pre)) ÷ x_pre ) % ( 2 ) ) = (((AbsDiff (y1_pre) (y2_pre)) ÷ y_pre ) % ( 2 ) ))) (PreH2 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) = 0)) (PreH3 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 1 )
.

Definition solver_return_wit_3 := 
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) <> 0)) (PreH2 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 0 ) ”
  &&  emp
) \/
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) <> 0)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 0 ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) <> 0)) (PreH2 : ((-100000) <= x1_pre)) (PreH3 : (x1_pre <= 100000)) (PreH4 : ((-100000) <= y1_pre)) (PreH5 : (y1_pre <= 100000)) (PreH6 : ((-100000) <= x2_pre)) (PreH7 : (x2_pre <= 100000)) (PreH8 : ((-100000) <= y2_pre)) (PreH9 : (y2_pre <= 100000)) (PreH10 : (1 <= x_pre)) (PreH11 : (x_pre <= 100000)) (PreH12 : (1 <= y_pre)) (PreH13 : (y_pre <= 100000)) ,
  (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 0 )
.

Definition solver_return_wit_4 := 
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) <> 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((AbsDiff (y1_pre) (y2_pre)) = (AbsDiff (y1_pre) (y2_pre)))) (PreH4 : ((-100000) <= x1_pre)) (PreH5 : (x1_pre <= 100000)) (PreH6 : ((-100000) <= y1_pre)) (PreH7 : (y1_pre <= 100000)) (PreH8 : ((-100000) <= x2_pre)) (PreH9 : (x2_pre <= 100000)) (PreH10 : ((-100000) <= y2_pre)) (PreH11 : (y2_pre <= 100000)) (PreH12 : (1 <= x_pre)) (PreH13 : (x_pre <= 100000)) (PreH14 : (1 <= y_pre)) (PreH15 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 0 ) ”
  &&  emp
) \/
(
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) <> 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  TT && emp 
|--
  “ (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 0 ) ”
  &&  emp
).

Definition solver_return_wit_4_split_goal_1 := 
forall (y_pre: Z) (x_pre: Z) (y2_pre: Z) (x2_pre: Z) (y1_pre: Z) (x1_pre: Z) (PreH1 : (((AbsDiff (y1_pre) (y2_pre)) % ( y_pre ) ) <> 0)) (PreH2 : (((AbsDiff (x1_pre) (x2_pre)) % ( x_pre ) ) = 0)) (PreH3 : ((-100000) <= x1_pre)) (PreH4 : (x1_pre <= 100000)) (PreH5 : ((-100000) <= y1_pre)) (PreH6 : (y1_pre <= 100000)) (PreH7 : ((-100000) <= x2_pre)) (PreH8 : (x2_pre <= 100000)) (PreH9 : ((-100000) <= y2_pre)) (PreH10 : (y2_pre <= 100000)) (PreH11 : (1 <= x_pre)) (PreH12 : (x_pre <= 100000)) (PreH13 : (1 <= y_pre)) (PreH14 : (y_pre <= 100000)) ,
  (Spec x1_pre y1_pre x2_pre y2_pre x_pre y_pre 0 )
.

Module Type VC_Correct.


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
Axiom proof_of_solver_entail_wit_1_1 : solver_entail_wit_1_1.
Axiom proof_of_solver_entail_wit_1_2 : solver_entail_wit_1_2.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_return_wit_4 : solver_return_wit_4.

End VC_Correct.
