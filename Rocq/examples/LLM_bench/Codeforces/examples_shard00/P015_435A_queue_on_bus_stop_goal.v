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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P015_435A_queue_on_bus_stop_lib.
Local Open Scope sac.

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (PreH1 : (1 <= (Zlength (groups_data)))) (PreH2 : ((Zlength (groups_data)) <= 100)) (PreH3 : (1 <= capacity_pre)) (PreH4 : (capacity_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (groups_data)))) -> ((1 <= (Znth i groups_data 0)) /\ ((Znth i groups_data 0) <= capacity_pre)))) (PreH6 : (n_pre = (Zlength (groups_data)))) ,
  ((( &( "used" ) )) # Int  |->_)
  **  ((( &( "buses" ) )) # Int  |-> 1)
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.full groups_pre n_pre groups_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (PreH1 : (1 <= (Zlength (groups_data)))) (PreH2 : ((Zlength (groups_data)) <= 100)) (PreH3 : (1 <= capacity_pre)) (PreH4 : (capacity_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (groups_data)))) -> ((1 <= (Znth i groups_data 0)) /\ ((Znth i groups_data 0) <= capacity_pre)))) (PreH6 : (n_pre = (Zlength (groups_data)))) ,
  ((( &( "buses" ) )) # Int  |->_)
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.full groups_pre n_pre groups_data )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (PreH1 : (1 <= (Zlength (groups_data)))) (PreH2 : ((Zlength (groups_data)) <= 100)) (PreH3 : (1 <= capacity_pre)) (PreH4 : (capacity_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (groups_data)))) -> ((1 <= (Znth i groups_data 0)) /\ ((Znth i groups_data 0) <= capacity_pre)))) (PreH6 : (n_pre = (Zlength (groups_data)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "used" ) )) # Int  |-> 0)
  **  ((( &( "buses" ) )) # Int  |-> 1)
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.full groups_pre n_pre groups_data )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (Zlength (groups_data)))) (PreH3 : ((Zlength (groups_data)) <= 100)) (PreH4 : (1 <= capacity_pre)) (PreH5 : (capacity_pre <= 100)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH7 : (n_pre = (Zlength (groups_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= buses)) (PreH11 : (buses <= (i + 1 ))) (PreH12 : (0 <= used)) (PreH13 : (used <= capacity_pre)) (PreH14 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buses" ) )) # Int  |-> buses)
  **  ((( &( "used" ) )) # Int  |-> used)
|--
  “ ((used + (Znth i groups_data 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (used + (Znth i groups_data 0) )) ”
.

Definition solver_safety_wit_5 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) > capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buses" ) )) # Int  |-> buses)
  **  ((( &( "used" ) )) # Int  |-> used)
|--
  “ ((buses + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (buses + 1 )) ”
.

Definition solver_safety_wit_6 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) > capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buses" ) )) # Int  |-> (buses + 1 ))
  **  ((( &( "used" ) )) # Int  |-> used)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) > capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buses" ) )) # Int  |-> (buses + 1 ))
  **  ((( &( "used" ) )) # Int  |-> 0)
|--
  “ ((0 + (Znth i groups_data 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + (Znth i groups_data 0) )) ”
.

Definition solver_safety_wit_8 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) <= capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buses" ) )) # Int  |-> buses)
  **  ((( &( "used" ) )) # Int  |-> used)
|--
  “ ((used + (Znth i groups_data 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (used + (Znth i groups_data 0) )) ”
.

Definition solver_safety_wit_9 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) > capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buses" ) )) # Int  |-> (buses + 1 ))
  **  ((( &( "used" ) )) # Int  |-> (0 + (Znth i groups_data 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) <= capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
  **  ((( &( "groups" ) )) # Ptr  |-> groups_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "buses" ) )) # Int  |-> buses)
  **  ((( &( "used" ) )) # Int  |-> (used + (Znth i groups_data 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (PreH1 : (1 <= (Zlength (groups_data)))) (PreH2 : ((Zlength (groups_data)) <= 100)) (PreH3 : (1 <= capacity_pre)) (PreH4 : (capacity_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (groups_data)))) -> ((1 <= (Znth i groups_data 0)) /\ ((Znth i groups_data 0) <= capacity_pre)))) (PreH6 : (n_pre = (Zlength (groups_data)))) ,
  (IntArray.full groups_pre n_pre groups_data )
|--
  “ (1 <= (Zlength (groups_data))) ” 
  &&  “ ((Zlength (groups_data)) <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre))) ” 
  &&  “ (n_pre = (Zlength (groups_data))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (0 + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (GreedyPrefixState (sublist (0) (0) (groups_data)) capacity_pre 1 0 ) ”
  &&  (IntArray.full groups_pre n_pre groups_data )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (groups_data: (@list Z)) (PreH1 : (1 <= (Zlength (groups_data)))) (PreH2 : ((Zlength (groups_data)) <= 100)) (PreH3 : (1 <= capacity_pre)) (PreH4 : (capacity_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (groups_data)))) -> ((1 <= (Znth i groups_data 0)) /\ ((Znth i groups_data 0) <= capacity_pre)))) (PreH6 : (n_pre = (Zlength (groups_data)))) ,
  TT && emp 
|--
  “ (GreedyPrefixState (sublist (0) (0) (groups_data)) capacity_pre 1 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_data: (@list Z)) (PreH1 : (1 <= (Zlength (groups_data)))) (PreH2 : ((Zlength (groups_data)) <= 100)) (PreH3 : (1 <= capacity_pre)) (PreH4 : (capacity_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (groups_data)))) -> ((1 <= (Znth i groups_data 0)) /\ ((Znth i groups_data 0) <= capacity_pre)))) (PreH6 : (n_pre = (Zlength (groups_data)))) ,
  (GreedyPrefixState (sublist (0) (0) (groups_data)) capacity_pre 1 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_data: (@list Z)) (PreH1 : (1 <= (Zlength (groups_data)))) (PreH2 : ((Zlength (groups_data)) <= 100)) (PreH3 : (1 <= capacity_pre)) (PreH4 : (capacity_pre <= 100)) (PreH5 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (groups_data)))) -> ((1 <= (Znth i groups_data 0)) /\ ((Znth i groups_data 0) <= capacity_pre)))) (PreH6 : (n_pre = (Zlength (groups_data)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))
.

Definition solver_entail_wit_2_1 := 
(
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) > capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
|--
  “ (1 <= (Zlength (groups_data))) ” 
  &&  “ ((Zlength (groups_data)) <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre))) ” 
  &&  “ (n_pre = (Zlength (groups_data))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (1 <= (buses + 1 )) ” 
  &&  “ ((buses + 1 ) <= ((i + 1 ) + 1 )) ” 
  &&  “ (0 <= (0 + (Znth i groups_data 0) )) ” 
  &&  “ ((0 + (Znth i groups_data 0) ) <= capacity_pre) ” 
  &&  “ (GreedyPrefixState (sublist (0) ((i + 1 )) (groups_data)) capacity_pre (buses + 1 ) (0 + (Znth i groups_data 0) ) ) ”
  &&  (IntArray.full groups_pre n_pre groups_data )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) > capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  TT && emp 
|--
  “ (GreedyPrefixState (sublist (0) ((i + 1 )) (groups_data)) capacity_pre (buses + 1 ) (0 + (Znth i groups_data 0) ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) > capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (GreedyPrefixState (sublist (0) ((i + 1 )) (groups_data)) capacity_pre (buses + 1 ) (0 + (Znth i groups_data 0) ) )
.

Definition solver_entail_wit_2_2 := 
(
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) <= capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
|--
  “ (1 <= (Zlength (groups_data))) ” 
  &&  “ ((Zlength (groups_data)) <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre))) ” 
  &&  “ (n_pre = (Zlength (groups_data))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (1 <= buses) ” 
  &&  “ (buses <= ((i + 1 ) + 1 )) ” 
  &&  “ (0 <= (used + (Znth i groups_data 0) )) ” 
  &&  “ ((used + (Znth i groups_data 0) ) <= capacity_pre) ” 
  &&  “ (GreedyPrefixState (sublist (0) ((i + 1 )) (groups_data)) capacity_pre buses (used + (Znth i groups_data 0) ) ) ”
  &&  (IntArray.full groups_pre n_pre groups_data )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) <= capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  TT && emp 
|--
  “ (GreedyPrefixState (sublist (0) ((i + 1 )) (groups_data)) capacity_pre buses (used + (Znth i groups_data 0) ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) <= capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (GreedyPrefixState (sublist (0) ((i + 1 )) (groups_data)) capacity_pre buses (used + (Znth i groups_data 0) ) )
.

Definition solver_return_wit_1 := 
(
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (groups_data)))) (PreH3 : ((Zlength (groups_data)) <= 100)) (PreH4 : (1 <= capacity_pre)) (PreH5 : (capacity_pre <= 100)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH7 : (n_pre = (Zlength (groups_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= buses)) (PreH11 : (buses <= (i + 1 ))) (PreH12 : (0 <= used)) (PreH13 : (used <= capacity_pre)) (PreH14 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
|--
  “ (Spec capacity_pre groups_data buses ) ”
  &&  (IntArray.full groups_pre n_pre groups_data )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (groups_data)))) (PreH3 : ((Zlength (groups_data)) <= 100)) (PreH4 : (1 <= capacity_pre)) (PreH5 : (capacity_pre <= 100)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH7 : (n_pre = (Zlength (groups_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= buses)) (PreH11 : (buses <= (i + 1 ))) (PreH12 : (0 <= used)) (PreH13 : (used <= capacity_pre)) (PreH14 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  TT && emp 
|--
  “ (Spec capacity_pre groups_data buses ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= (Zlength (groups_data)))) (PreH3 : ((Zlength (groups_data)) <= 100)) (PreH4 : (1 <= capacity_pre)) (PreH5 : (capacity_pre <= 100)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH7 : (n_pre = (Zlength (groups_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= buses)) (PreH11 : (buses <= (i + 1 ))) (PreH12 : (0 <= used)) (PreH13 : (used <= capacity_pre)) (PreH14 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (Spec capacity_pre groups_data buses )
.

Definition solver_partial_solve_wit_1 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (1 <= (Zlength (groups_data)))) (PreH3 : ((Zlength (groups_data)) <= 100)) (PreH4 : (1 <= capacity_pre)) (PreH5 : (capacity_pre <= 100)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH7 : (n_pre = (Zlength (groups_data)))) (PreH8 : (0 <= i)) (PreH9 : (i <= n_pre)) (PreH10 : (1 <= buses)) (PreH11 : (buses <= (i + 1 ))) (PreH12 : (0 <= used)) (PreH13 : (used <= capacity_pre)) (PreH14 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= (Zlength (groups_data))) ” 
  &&  “ ((Zlength (groups_data)) <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre))) ” 
  &&  “ (n_pre = (Zlength (groups_data))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= buses) ” 
  &&  “ (buses <= (i + 1 )) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= capacity_pre) ” 
  &&  “ (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used ) ”
  &&  (((groups_pre + (i * sizeof(INT)))) # Int  |-> (Znth i groups_data 0))
  **  (IntArray.missing_i groups_pre i 0 n_pre groups_data )
.

Definition solver_partial_solve_wit_2 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) > capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
|--
  “ ((used + (Znth i groups_data 0) ) > capacity_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= (Zlength (groups_data))) ” 
  &&  “ ((Zlength (groups_data)) <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre))) ” 
  &&  “ (n_pre = (Zlength (groups_data))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= buses) ” 
  &&  “ (buses <= (i + 1 )) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= capacity_pre) ” 
  &&  “ (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used ) ”
  &&  (((groups_pre + (i * sizeof(INT)))) # Int  |-> (Znth i groups_data 0))
  **  (IntArray.missing_i groups_pre i 0 n_pre groups_data )
.

Definition solver_partial_solve_wit_3 := 
forall (capacity_pre: Z) (n_pre: Z) (groups_pre: Z) (groups_data: (@list Z)) (used: Z) (buses: Z) (i: Z) (PreH1 : ((used + (Znth i groups_data 0) ) <= capacity_pre)) (PreH2 : (i < n_pre)) (PreH3 : (1 <= (Zlength (groups_data)))) (PreH4 : ((Zlength (groups_data)) <= 100)) (PreH5 : (1 <= capacity_pre)) (PreH6 : (capacity_pre <= 100)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre)))) (PreH8 : (n_pre = (Zlength (groups_data)))) (PreH9 : (0 <= i)) (PreH10 : (i <= n_pre)) (PreH11 : (1 <= buses)) (PreH12 : (buses <= (i + 1 ))) (PreH13 : (0 <= used)) (PreH14 : (used <= capacity_pre)) (PreH15 : (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used )) ,
  (IntArray.full groups_pre n_pre groups_data )
|--
  “ ((used + (Znth i groups_data 0) ) <= capacity_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= (Zlength (groups_data))) ” 
  &&  “ ((Zlength (groups_data)) <= 100) ” 
  &&  “ (1 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 100) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (groups_data)))) -> ((1 <= (Znth k groups_data 0)) /\ ((Znth k groups_data 0) <= capacity_pre))) ” 
  &&  “ (n_pre = (Zlength (groups_data))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= buses) ” 
  &&  “ (buses <= (i + 1 )) ” 
  &&  “ (0 <= used) ” 
  &&  “ (used <= capacity_pre) ” 
  &&  “ (GreedyPrefixState (sublist (0) (i) (groups_data)) capacity_pre buses used ) ”
  &&  (((groups_pre + (i * sizeof(INT)))) # Int  |-> (Znth i groups_data 0))
  **  (IntArray.missing_i groups_pre i 0 n_pre groups_data )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.

End VC_Correct.
