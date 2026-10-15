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
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P023_985A_chess_placing_lib.
Local Open Scope sac.

(*----- Function iabs -----*)

Definition iabs_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-100) <= x_pre)) (PreH3 : (x_pre <= 100)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition iabs_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : ((-100) <= x_pre)) (PreH2 : (x_pre <= 100)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition iabs_return_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-100) <= x_pre)) (PreH3 : (x_pre <= 100)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-100) <= x_pre)) (PreH3 : (x_pre <= 100)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Z.abs (x_pre))) ”
  &&  emp
).

Definition iabs_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : ((-100) <= x_pre)) (PreH3 : (x_pre <= 100)) ,
  ((-x_pre) = (Z.abs (x_pre)))
.

Definition iabs_return_wit_2 := 
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-100) <= x_pre)) (PreH3 : (x_pre <= 100)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-100) <= x_pre)) (PreH3 : (x_pre <= 100)) ,
  TT && emp 
|--
  “ (x_pre = (Z.abs (x_pre))) ”
  &&  emp
).

Definition iabs_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : ((-100) <= x_pre)) (PreH3 : (x_pre <= 100)) ,
  (x_pre = (Z.abs (x_pre)))
.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation positions l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH7 : (half_pre = (Zlength (positions)))) ,
  ((( &( "even" ) )) # Int64  |->_)
  **  ((( &( "odd" ) )) # Int64  |-> 0)
  **  (IntArray.full p_pre half_pre l1 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation positions l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH7 : (half_pre = (Zlength (positions)))) ,
  ((( &( "odd" ) )) # Int64  |->_)
  **  (IntArray.full p_pre half_pre l1 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation positions l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH7 : (half_pre = (Zlength (positions)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "even" ) )) # Int64  |-> 0)
  **  ((( &( "odd" ) )) # Int64  |-> 0)
  **  (IntArray.full p_pre half_pre l1 )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
(
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((odd + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (odd + retval )) ”
) \/
(
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((odd + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (odd + retval )) ”
).

Definition solver_safety_wit_4_split_goal_1 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((odd + retval ) <= INT64_MAX) ”
.

Definition solver_safety_wit_4_split_goal_2 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((INT64_MIN) <= (odd + retval )) ”
.

Definition solver_safety_wit_5 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < half_pre)) (PreH2 : (2 <= (2 * half_pre ))) (PreH3 : ((2 * half_pre ) <= 100)) (PreH4 : (Pre (2 * half_pre ) positions )) (PreH5 : (half_pre = (Zlength (positions)))) (PreH6 : ((Zlength (sorted)) = half_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH8 : (Permutation positions sorted )) (PreH9 : (mono_nondec sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= half_pre)) (PreH12 : (0 <= odd)) (PreH13 : (odd <= (100 * i ))) (PreH14 : (0 <= even)) (PreH15 : (even <= (100 * i ))) (PreH16 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ (((Znth i sorted 0) - ((2 * i ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i sorted 0) - ((2 * i ) + 1 ) )) ”
.

Definition solver_safety_wit_6 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < half_pre)) (PreH2 : (2 <= (2 * half_pre ))) (PreH3 : ((2 * half_pre ) <= 100)) (PreH4 : (Pre (2 * half_pre ) positions )) (PreH5 : (half_pre = (Zlength (positions)))) (PreH6 : ((Zlength (sorted)) = half_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH8 : (Permutation positions sorted )) (PreH9 : (mono_nondec sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= half_pre)) (PreH12 : (0 <= odd)) (PreH13 : (odd <= (100 * i ))) (PreH14 : (0 <= even)) (PreH15 : (even <= (100 * i ))) (PreH16 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition solver_safety_wit_7 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < half_pre)) (PreH2 : (2 <= (2 * half_pre ))) (PreH3 : ((2 * half_pre ) <= 100)) (PreH4 : (Pre (2 * half_pre ) positions )) (PreH5 : (half_pre = (Zlength (positions)))) (PreH6 : ((Zlength (sorted)) = half_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH8 : (Permutation positions sorted )) (PreH9 : (mono_nondec sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= half_pre)) (PreH12 : (0 <= odd)) (PreH13 : (odd <= (100 * i ))) (PreH14 : (0 <= even)) (PreH15 : (even <= (100 * i ))) (PreH16 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition solver_safety_wit_8 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < half_pre)) (PreH2 : (2 <= (2 * half_pre ))) (PreH3 : ((2 * half_pre ) <= 100)) (PreH4 : (Pre (2 * half_pre ) positions )) (PreH5 : (half_pre = (Zlength (positions)))) (PreH6 : ((Zlength (sorted)) = half_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH8 : (Permutation positions sorted )) (PreH9 : (mono_nondec sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= half_pre)) (PreH12 : (0 <= odd)) (PreH13 : (odd <= (100 * i ))) (PreH14 : (0 <= even)) (PreH15 : (even <= (100 * i ))) (PreH16 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_9 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < half_pre)) (PreH2 : (2 <= (2 * half_pre ))) (PreH3 : ((2 * half_pre ) <= 100)) (PreH4 : (Pre (2 * half_pre ) positions )) (PreH5 : (half_pre = (Zlength (positions)))) (PreH6 : ((Zlength (sorted)) = half_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH8 : (Permutation positions sorted )) (PreH9 : (mono_nondec sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= half_pre)) (PreH12 : (0 <= odd)) (PreH13 : (odd <= (100 * i ))) (PreH14 : (0 <= even)) (PreH15 : (even <= (100 * i ))) (PreH16 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_10 := 
(
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval_2 = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval_2 ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((even + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (even + retval )) ”
) \/
(
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval_2 = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval_2 ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((even + retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (even + retval )) ”
).

Definition solver_safety_wit_10_split_goal_1 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval_2 = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval_2 ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((even + retval ) <= INT64_MAX) ”
.

Definition solver_safety_wit_10_split_goal_2 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval_2 = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval_2 ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((INT64_MIN) <= (even + retval )) ”
.

Definition solver_safety_wit_11 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ (((Znth i sorted 0) - ((2 * i ) + 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i sorted 0) - ((2 * i ) + 2 ) )) ”
.

Definition solver_safety_wit_12 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ (((2 * i ) + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 2 )) ”
.

Definition solver_safety_wit_13 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition solver_safety_wit_14 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_15 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition solver_safety_wit_16 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted )) (PreH11 : (mono_nondec sorted )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval ))
  **  ((( &( "even" ) )) # Int64  |-> (even + retval_2 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation positions l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH7 : (half_pre = (Zlength (positions)))) ,
  (IntArray.full p_pre half_pre l1 )
|--
  EX (sorted: (@list Z)) ,
  “ (2 <= (2 * half_pre )) ” 
  &&  “ ((2 * half_pre ) <= 100) ” 
  &&  “ (Pre (2 * half_pre ) positions ) ” 
  &&  “ (half_pre = (Zlength (positions))) ” 
  &&  “ ((Zlength (sorted)) = half_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre )))) ” 
  &&  “ (Permutation positions sorted ) ” 
  &&  “ (mono_nondec sorted ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= half_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (100 * 0 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (100 * 0 )) ” 
  &&  “ (ChessCostPrefix sorted 0 0 0 ) ”
  &&  (IntArray.full p_pre half_pre sorted )
) \/
(
forall (half_pre: Z) (positions: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation positions l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH7 : (half_pre = (Zlength (positions)))) ,
  TT && emp 
|--
  “ (ChessCostPrefix l1 0 0 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k l1 0)) /\ ((Znth k l1 0) <= (2 * half_pre )))) ” 
  &&  “ ((Zlength (l1)) = half_pre) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (half_pre: Z) (positions: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation positions l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH7 : (half_pre = (Zlength (positions)))) ,
  (ChessCostPrefix l1 0 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (half_pre: Z) (positions: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation positions l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH7 : (half_pre = (Zlength (positions)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k l1 0)) /\ ((Znth k l1 0) <= (2 * half_pre ))))
.

Definition solver_entail_wit_1_split_goal_3 := 
forall (half_pre: Z) (positions: (@list Z)) (l1: (@list Z)) (PreH1 : (Permutation positions l1 )) (PreH2 : (mono_nondec l1 )) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH7 : (half_pre = (Zlength (positions)))) ,
  ((Zlength (l1)) = half_pre)
.

Definition solver_entail_wit_2 := 
(
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted_2: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted_2)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted_2 )) (PreH11 : (mono_nondec sorted_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted_2 i odd even )) ,
  (IntArray.full p_pre half_pre sorted_2 )
|--
  EX (sorted: (@list Z)) ,
  “ (2 <= (2 * half_pre )) ” 
  &&  “ ((2 * half_pre ) <= 100) ” 
  &&  “ (Pre (2 * half_pre ) positions ) ” 
  &&  “ (half_pre = (Zlength (positions))) ” 
  &&  “ ((Zlength (sorted)) = half_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre )))) ” 
  &&  “ (Permutation positions sorted ) ” 
  &&  “ (mono_nondec sorted ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= half_pre) ” 
  &&  “ (0 <= (odd + retval )) ” 
  &&  “ ((odd + retval ) <= (100 * (i + 1 ) )) ” 
  &&  “ (0 <= (even + retval_2 )) ” 
  &&  “ ((even + retval_2 ) <= (100 * (i + 1 ) )) ” 
  &&  “ (ChessCostPrefix sorted (i + 1 ) (odd + retval ) (even + retval_2 ) ) ”
  &&  (IntArray.full p_pre half_pre sorted )
) \/
(
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted_2: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted_2)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted_2 )) (PreH11 : (mono_nondec sorted_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted_2 i odd even )) ,
  TT && emp 
|--
  “ (ChessCostPrefix sorted_2 (i + 1 ) (odd + retval ) (even + retval_2 ) ) ” 
  &&  “ ((even + retval_2 ) <= (100 * (i + 1 ) )) ” 
  &&  “ (0 <= (even + retval_2 )) ” 
  &&  “ ((odd + retval ) <= (100 * (i + 1 ) )) ” 
  &&  “ (0 <= (odd + retval )) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted_2: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted_2)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted_2 )) (PreH11 : (mono_nondec sorted_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted_2 i odd even )) ,
  (ChessCostPrefix sorted_2 (i + 1 ) (odd + retval ) (even + retval_2 ) )
.

Definition solver_entail_wit_2_split_goal_2 := 
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted_2: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted_2)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted_2 )) (PreH11 : (mono_nondec sorted_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted_2 i odd even )) ,
  ((even + retval_2 ) <= (100 * (i + 1 ) ))
.

Definition solver_entail_wit_2_split_goal_3 := 
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted_2: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted_2)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted_2 )) (PreH11 : (mono_nondec sorted_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted_2 i odd even )) ,
  (0 <= (even + retval_2 ))
.

Definition solver_entail_wit_2_split_goal_4 := 
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted_2: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted_2)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted_2 )) (PreH11 : (mono_nondec sorted_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted_2 i odd even )) ,
  ((odd + retval ) <= (100 * (i + 1 ) ))
.

Definition solver_entail_wit_2_split_goal_5 := 
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted_2: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 2 ) ))))) (PreH2 : (retval = (Z.abs (((Znth i sorted_2 0) - ((2 * i ) + 1 ) ))))) (PreH3 : (i < half_pre)) (PreH4 : (2 <= (2 * half_pre ))) (PreH5 : ((2 * half_pre ) <= 100)) (PreH6 : (Pre (2 * half_pre ) positions )) (PreH7 : (half_pre = (Zlength (positions)))) (PreH8 : ((Zlength (sorted_2)) = half_pre)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= (2 * half_pre ))))) (PreH10 : (Permutation positions sorted_2 )) (PreH11 : (mono_nondec sorted_2 )) (PreH12 : (0 <= i)) (PreH13 : (i <= half_pre)) (PreH14 : (0 <= odd)) (PreH15 : (odd <= (100 * i ))) (PreH16 : (0 <= even)) (PreH17 : (even <= (100 * i ))) (PreH18 : (ChessCostPrefix sorted_2 i odd even )) ,
  (0 <= (odd + retval ))
.

Definition solver_return_wit_1 := 
(
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (odd < even)) (PreH2 : (i >= half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
|--
  EX (p_after: (@list Z)) ,
  “ (Spec (2 * half_pre ) positions odd ) ” 
  &&  “ (Permutation positions p_after ) ”
  &&  (IntArray.full p_pre half_pre p_after )
) \/
(
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (odd < even)) (PreH2 : (i >= half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  TT && emp 
|--
  “ (Spec (2 * half_pre ) positions odd ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (odd < even)) (PreH2 : (i >= half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (Spec (2 * half_pre ) positions odd )
.

Definition solver_return_wit_2 := 
(
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (odd >= even)) (PreH2 : (i >= half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
|--
  EX (p_after: (@list Z)) ,
  “ (Spec (2 * half_pre ) positions even ) ” 
  &&  “ (Permutation positions p_after ) ”
  &&  (IntArray.full p_pre half_pre p_after )
) \/
(
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (odd >= even)) (PreH2 : (i >= half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  TT && emp 
|--
  “ (Spec (2 * half_pre ) positions even ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (half_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (odd >= even)) (PreH2 : (i >= half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (Spec (2 * half_pre ) positions even )
.

Definition solver_partial_solve_wit_1_pure := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (PreH1 : (2 <= (2 * half_pre ))) (PreH2 : ((2 * half_pre ) <= 100)) (PreH3 : (Pre (2 * half_pre ) positions )) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH5 : (half_pre = (Zlength (positions)))) ,
  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  (IntArray.full p_pre half_pre positions )
|--
  “ (0 <= half_pre) ” 
  &&  “ (half_pre <= 50000) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (PreH1 : (2 <= (2 * half_pre ))) (PreH2 : ((2 * half_pre ) <= 100)) (PreH3 : (Pre (2 * half_pre ) positions )) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre ))))) (PreH5 : (half_pre = (Zlength (positions)))) ,
  (IntArray.full p_pre half_pre positions )
|--
  “ (0 <= half_pre) ” 
  &&  “ (half_pre <= 50000) ” 
  &&  “ (2 <= (2 * half_pre )) ” 
  &&  “ ((2 * half_pre ) <= 100) ” 
  &&  “ (Pre (2 * half_pre ) positions ) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < half_pre)) -> ((1 <= (Znth i positions 0)) /\ ((Znth i positions 0) <= (2 * half_pre )))) ” 
  &&  “ (half_pre = (Zlength (positions))) ”
  &&  (IntArray.full p_pre half_pre positions )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < half_pre)) (PreH2 : (2 <= (2 * half_pre ))) (PreH3 : ((2 * half_pre ) <= 100)) (PreH4 : (Pre (2 * half_pre ) positions )) (PreH5 : (half_pre = (Zlength (positions)))) (PreH6 : ((Zlength (sorted)) = half_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH8 : (Permutation positions sorted )) (PreH9 : (mono_nondec sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= half_pre)) (PreH12 : (0 <= odd)) (PreH13 : (odd <= (100 * i ))) (PreH14 : (0 <= even)) (PreH15 : (even <= (100 * i ))) (PreH16 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
|--
  “ (i < half_pre) ” 
  &&  “ (2 <= (2 * half_pre )) ” 
  &&  “ ((2 * half_pre ) <= 100) ” 
  &&  “ (Pre (2 * half_pre ) positions ) ” 
  &&  “ (half_pre = (Zlength (positions))) ” 
  &&  “ ((Zlength (sorted)) = half_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre )))) ” 
  &&  “ (Permutation positions sorted ) ” 
  &&  “ (mono_nondec sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= half_pre) ” 
  &&  “ (0 <= odd) ” 
  &&  “ (odd <= (100 * i )) ” 
  &&  “ (0 <= even) ” 
  &&  “ (even <= (100 * i )) ” 
  &&  “ (ChessCostPrefix sorted i odd even ) ”
  &&  (((p_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i p_pre i 0 half_pre sorted )
.

Definition solver_partial_solve_wit_3_pure := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < half_pre)) (PreH2 : (2 <= (2 * half_pre ))) (PreH3 : ((2 * half_pre ) <= 100)) (PreH4 : (Pre (2 * half_pre ) positions )) (PreH5 : (half_pre = (Zlength (positions)))) (PreH6 : ((Zlength (sorted)) = half_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH8 : (Permutation positions sorted )) (PreH9 : (mono_nondec sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= half_pre)) (PreH12 : (0 <= odd)) (PreH13 : (odd <= (100 * i ))) (PreH14 : (0 <= even)) (PreH15 : (even <= (100 * i ))) (PreH16 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> odd)
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((-100) <= ((Znth i sorted 0) - ((2 * i ) + 1 ) )) ” 
  &&  “ (((Znth i sorted 0) - ((2 * i ) + 1 ) ) <= 100) ”
.

Definition solver_partial_solve_wit_3_aux := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < half_pre)) (PreH2 : (2 <= (2 * half_pre ))) (PreH3 : ((2 * half_pre ) <= 100)) (PreH4 : (Pre (2 * half_pre ) positions )) (PreH5 : (half_pre = (Zlength (positions)))) (PreH6 : ((Zlength (sorted)) = half_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH8 : (Permutation positions sorted )) (PreH9 : (mono_nondec sorted )) (PreH10 : (0 <= i)) (PreH11 : (i <= half_pre)) (PreH12 : (0 <= odd)) (PreH13 : (odd <= (100 * i ))) (PreH14 : (0 <= even)) (PreH15 : (even <= (100 * i ))) (PreH16 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
|--
  “ ((-100) <= ((Znth i sorted 0) - ((2 * i ) + 1 ) )) ” 
  &&  “ (((Znth i sorted 0) - ((2 * i ) + 1 ) ) <= 100) ” 
  &&  “ (i < half_pre) ” 
  &&  “ (2 <= (2 * half_pre )) ” 
  &&  “ ((2 * half_pre ) <= 100) ” 
  &&  “ (Pre (2 * half_pre ) positions ) ” 
  &&  “ (half_pre = (Zlength (positions))) ” 
  &&  “ ((Zlength (sorted)) = half_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre )))) ” 
  &&  “ (Permutation positions sorted ) ” 
  &&  “ (mono_nondec sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= half_pre) ” 
  &&  “ (0 <= odd) ” 
  &&  “ (odd <= (100 * i )) ” 
  &&  “ (0 <= even) ” 
  &&  “ (even <= (100 * i )) ” 
  &&  “ (ChessCostPrefix sorted i odd even ) ”
  &&  (IntArray.full p_pre half_pre sorted )
.

Definition solver_partial_solve_wit_3 := solver_partial_solve_wit_3_pure -> solver_partial_solve_wit_3_aux.

Definition solver_partial_solve_wit_4 := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
|--
  “ (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) )))) ” 
  &&  “ (i < half_pre) ” 
  &&  “ (2 <= (2 * half_pre )) ” 
  &&  “ ((2 * half_pre ) <= 100) ” 
  &&  “ (Pre (2 * half_pre ) positions ) ” 
  &&  “ (half_pre = (Zlength (positions))) ” 
  &&  “ ((Zlength (sorted)) = half_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre )))) ” 
  &&  “ (Permutation positions sorted ) ” 
  &&  “ (mono_nondec sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= half_pre) ” 
  &&  “ (0 <= odd) ” 
  &&  “ (odd <= (100 * i )) ” 
  &&  “ (0 <= even) ” 
  &&  “ (even <= (100 * i )) ” 
  &&  “ (ChessCostPrefix sorted i odd even ) ”
  &&  (((p_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i p_pre i 0 half_pre sorted )
.

Definition solver_partial_solve_wit_5_pure := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "half" ) )) # Int  |-> half_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "odd" ) )) # Int64  |-> (odd + retval ))
  **  ((( &( "even" ) )) # Int64  |-> even)
|--
  “ ((-100) <= ((Znth i sorted 0) - ((2 * i ) + 2 ) )) ” 
  &&  “ (((Znth i sorted 0) - ((2 * i ) + 2 ) ) <= 100) ”
.

Definition solver_partial_solve_wit_5_aux := 
forall (half_pre: Z) (p_pre: Z) (positions: (@list Z)) (even: Z) (odd: Z) (i: Z) (sorted: (@list Z)) (retval: Z) (PreH1 : (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) ))))) (PreH2 : (i < half_pre)) (PreH3 : (2 <= (2 * half_pre ))) (PreH4 : ((2 * half_pre ) <= 100)) (PreH5 : (Pre (2 * half_pre ) positions )) (PreH6 : (half_pre = (Zlength (positions)))) (PreH7 : ((Zlength (sorted)) = half_pre)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre ))))) (PreH9 : (Permutation positions sorted )) (PreH10 : (mono_nondec sorted )) (PreH11 : (0 <= i)) (PreH12 : (i <= half_pre)) (PreH13 : (0 <= odd)) (PreH14 : (odd <= (100 * i ))) (PreH15 : (0 <= even)) (PreH16 : (even <= (100 * i ))) (PreH17 : (ChessCostPrefix sorted i odd even )) ,
  (IntArray.full p_pre half_pre sorted )
|--
  “ ((-100) <= ((Znth i sorted 0) - ((2 * i ) + 2 ) )) ” 
  &&  “ (((Znth i sorted 0) - ((2 * i ) + 2 ) ) <= 100) ” 
  &&  “ (retval = (Z.abs (((Znth i sorted 0) - ((2 * i ) + 1 ) )))) ” 
  &&  “ (i < half_pre) ” 
  &&  “ (2 <= (2 * half_pre )) ” 
  &&  “ ((2 * half_pre ) <= 100) ” 
  &&  “ (Pre (2 * half_pre ) positions ) ” 
  &&  “ (half_pre = (Zlength (positions))) ” 
  &&  “ ((Zlength (sorted)) = half_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < half_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= (2 * half_pre )))) ” 
  &&  “ (Permutation positions sorted ) ” 
  &&  “ (mono_nondec sorted ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= half_pre) ” 
  &&  “ (0 <= odd) ” 
  &&  “ (odd <= (100 * i )) ” 
  &&  “ (0 <= even) ” 
  &&  “ (even <= (100 * i )) ” 
  &&  “ (ChessCostPrefix sorted i odd even ) ”
  &&  (IntArray.full p_pre half_pre sorted )
.

Definition solver_partial_solve_wit_5 := solver_partial_solve_wit_5_pure -> solver_partial_solve_wit_5_aux.

Module Type VC_Correct.


Axiom proof_of_iabs_safety_wit_1 : iabs_safety_wit_1.
Axiom proof_of_iabs_safety_wit_2 : iabs_safety_wit_2.
Axiom proof_of_iabs_return_wit_1 : iabs_return_wit_1.
Axiom proof_of_iabs_return_wit_2 : iabs_return_wit_2.
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3_pure : solver_partial_solve_wit_3_pure.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5_pure : solver_partial_solve_wit_5_pure.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.

End VC_Correct.
