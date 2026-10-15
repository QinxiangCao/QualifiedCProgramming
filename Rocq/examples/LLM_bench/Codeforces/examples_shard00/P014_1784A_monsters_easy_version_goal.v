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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P014_1784A_monsters_easy_version_lib.
Local Open Scope sac.

(*----- Function cmp_int -----*)

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (Permutation input sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input)))))) ,
  ((( &( "spent" ) )) # Int64  |->_)
  **  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (Permutation input sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input)))))) ,
  ((( &( "kept" ) )) # Int  |->_)
  **  ((( &( "spent" ) )) # Int64  |-> 0)
  **  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (Permutation input sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input)))))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "kept" ) )) # Int  |-> 0)
  **  ((( &( "spent" ) )) # Int64  |-> 0)
  **  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullPreparationSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= kept)) (PreH13 : (kept <= i)) (PreH14 : (0 <= spent)) (PreH15 : (spent <= (i * n_pre ))) (PreH16 : (PrefixGreedyState input sorted i kept spent )) ,
  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "spent" ) )) # Int64  |-> spent)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ ((kept + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (kept + 1 )) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullPreparationSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= kept)) (PreH13 : (kept <= i)) (PreH14 : (0 <= spent)) (PreH15 : (spent <= (i * n_pre ))) (PreH16 : (PrefixGreedyState input sorted i kept spent )) ,
  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "spent" ) )) # Int64  |-> spent)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((kept + 1 ) > (Znth i sorted 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullPreparationSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "next" ) )) # Int  |-> (Znth i sorted 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "spent" ) )) # Int64  |-> spent)
|--
  “ ((spent + ((Znth i sorted 0) - (Znth i sorted 0) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (spent + ((Znth i sorted 0) - (Znth i sorted 0) ) )) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((kept + 1 ) > (Znth i sorted 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullPreparationSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "next" ) )) # Int  |-> (Znth i sorted 0))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "spent" ) )) # Int64  |-> spent)
|--
  “ (((Znth i sorted 0) - (Znth i sorted 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i sorted 0) - (Znth i sorted 0) )) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((kept + 1 ) <= (Znth i sorted 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullPreparationSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "next" ) )) # Int  |-> (kept + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "spent" ) )) # Int64  |-> spent)
|--
  “ ((spent + ((Znth i sorted 0) - (kept + 1 ) ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (spent + ((Znth i sorted 0) - (kept + 1 ) ) )) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((kept + 1 ) <= (Znth i sorted 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullPreparationSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "next" ) )) # Int  |-> (kept + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> kept)
  **  ((( &( "spent" ) )) # Int64  |-> spent)
|--
  “ (((Znth i sorted 0) - (kept + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i sorted 0) - (kept + 1 ) )) ”
.

Definition solver_safety_wit_10 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((kept + 1 ) > (Znth i sorted 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullPreparationSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> (Znth i sorted 0))
  **  ((( &( "spent" ) )) # Int64  |-> (spent + ((Znth i sorted 0) - (Znth i sorted 0) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_11 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((kept + 1 ) <= (Znth i sorted 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullPreparationSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "kept" ) )) # Int  |-> (kept + 1 ))
  **  ((( &( "spent" ) )) # Int64  |-> (spent + ((Znth i sorted 0) - (kept + 1 ) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (Permutation input sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted_2 )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input)))))) ,
  (IntArray.full a_pre n_pre sorted_2 )
|--
  EX (sorted: (@list Z)) ,
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullPreparationSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (0 * n_pre )) ” 
  &&  “ (PrefixGreedyState input sorted 0 0 0 ) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (Permutation input sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted_2 )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input)))))) ,
  TT && emp 
|--
  “ (PrefixGreedyState input sorted_2 0 0 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (Permutation input sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted_2 )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input)))))) ,
  (PrefixGreedyState input sorted_2 0 0 0 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (PreH1 : (Permutation input sorted_2 )) (PreH2 : (increasing sorted_2 )) (PreH3 : ((Zlength (sorted_2)) = n_pre)) (PreH4 : (FullPreparationSpecBridge input sorted_2 )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input)))))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre)))
.

Definition solver_entail_wit_2_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((kept + 1 ) > (Znth i sorted_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullPreparationSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent )) ,
  (IntArray.full a_pre n_pre sorted_2 )
|--
  EX (sorted: (@list Z)) ,
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullPreparationSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (Znth i sorted_2 0)) ” 
  &&  “ ((Znth i sorted_2 0) <= (i + 1 )) ” 
  &&  “ (0 <= (spent + ((Znth i sorted_2 0) - (Znth i sorted_2 0) ) )) ” 
  &&  “ ((spent + ((Znth i sorted_2 0) - (Znth i sorted_2 0) ) ) <= ((i + 1 ) * n_pre )) ” 
  &&  “ (PrefixGreedyState input sorted (i + 1 ) (Znth i sorted_2 0) (spent + ((Znth i sorted_2 0) - (Znth i sorted_2 0) ) ) ) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((kept + 1 ) > (Znth i sorted_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullPreparationSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent )) ,
  TT && emp 
|--
  “ (PrefixGreedyState input sorted_2 (i + 1 ) (Znth i sorted_2 0) (spent + ((Znth i sorted_2 0) - (Znth i sorted_2 0) ) ) ) ” 
  &&  “ ((spent + ((Znth i sorted_2 0) - (Znth i sorted_2 0) ) ) <= ((i + 1 ) * n_pre )) ”
  &&  emp
).

Definition solver_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((kept + 1 ) > (Znth i sorted_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullPreparationSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent )) ,
  (PrefixGreedyState input sorted_2 (i + 1 ) (Znth i sorted_2 0) (spent + ((Znth i sorted_2 0) - (Znth i sorted_2 0) ) ) )
.

Definition solver_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((kept + 1 ) > (Znth i sorted_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullPreparationSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent )) ,
  ((spent + ((Znth i sorted_2 0) - (Znth i sorted_2 0) ) ) <= ((i + 1 ) * n_pre ))
.

Definition solver_entail_wit_2_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((kept + 1 ) <= (Znth i sorted_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullPreparationSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent )) ,
  (IntArray.full a_pre n_pre sorted_2 )
|--
  EX (sorted: (@list Z)) ,
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullPreparationSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (kept + 1 )) ” 
  &&  “ ((kept + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= (spent + ((Znth i sorted_2 0) - (kept + 1 ) ) )) ” 
  &&  “ ((spent + ((Znth i sorted_2 0) - (kept + 1 ) ) ) <= ((i + 1 ) * n_pre )) ” 
  &&  “ (PrefixGreedyState input sorted (i + 1 ) (kept + 1 ) (spent + ((Znth i sorted_2 0) - (kept + 1 ) ) ) ) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((kept + 1 ) <= (Znth i sorted_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullPreparationSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent )) ,
  TT && emp 
|--
  “ (PrefixGreedyState input sorted_2 (i + 1 ) (kept + 1 ) (spent + ((Znth i sorted_2 0) - (kept + 1 ) ) ) ) ” 
  &&  “ ((spent + ((Znth i sorted_2 0) - (kept + 1 ) ) ) <= ((i + 1 ) * n_pre )) ”
  &&  emp
).

Definition solver_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((kept + 1 ) <= (Znth i sorted_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullPreparationSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent )) ,
  (PrefixGreedyState input sorted_2 (i + 1 ) (kept + 1 ) (spent + ((Znth i sorted_2 0) - (kept + 1 ) ) ) )
.

Definition solver_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((kept + 1 ) <= (Znth i sorted_2 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullPreparationSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted_2 i kept spent )) ,
  ((spent + ((Znth i sorted_2 0) - (kept + 1 ) ) ) <= ((i + 1 ) * n_pre ))
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullPreparationSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= kept)) (PreH13 : (kept <= i)) (PreH14 : (0 <= spent)) (PreH15 : (spent <= (i * n_pre ))) (PreH16 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  EX (post: (@list Z)) ,
  “ (Spec input spent ) ”
  &&  (IntArray.full a_pre n_pre post )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullPreparationSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= kept)) (PreH13 : (kept <= i)) (PreH14 : (0 <= spent)) (PreH15 : (spent <= (i * n_pre ))) (PreH16 : (PrefixGreedyState input sorted i kept spent )) ,
  TT && emp 
|--
  “ (Spec input spent ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullPreparationSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= kept)) (PreH13 : (kept <= i)) (PreH14 : (0 <= spent)) (PreH15 : (spent <= (i * n_pre ))) (PreH16 : (PrefixGreedyState input sorted i kept spent )) ,
  (Spec input spent )
.

Definition solver_partial_solve_wit_1_pure := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input)))))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (n_pre = (Zlength (input))) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input)))))) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= (Zlength (input))) ” 
  &&  “ ((Zlength (input)) <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= (Zlength (input))))) ”
  &&  (IntArray.full a_pre n_pre input )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullPreparationSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= kept)) (PreH13 : (kept <= i)) (PreH14 : (0 <= spent)) (PreH15 : (spent <= (i * n_pre ))) (PreH16 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullPreparationSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= kept) ” 
  &&  “ (kept <= i) ” 
  &&  “ (0 <= spent) ” 
  &&  “ (spent <= (i * n_pre )) ” 
  &&  “ (PrefixGreedyState input sorted i kept spent ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i a_pre i 0 n_pre sorted )
.

Definition solver_partial_solve_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((kept + 1 ) > (Znth i sorted 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullPreparationSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  “ ((kept + 1 ) > (Znth i sorted 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullPreparationSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= kept) ” 
  &&  “ (kept <= i) ” 
  &&  “ (0 <= spent) ” 
  &&  “ (spent <= (i * n_pre )) ” 
  &&  “ (PrefixGreedyState input sorted i kept spent ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i a_pre i 0 n_pre sorted )
.

Definition solver_partial_solve_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((kept + 1 ) > (Znth i sorted 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullPreparationSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  “ ((kept + 1 ) > (Znth i sorted 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullPreparationSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= kept) ” 
  &&  “ (kept <= i) ” 
  &&  “ (0 <= spent) ” 
  &&  “ (spent <= (i * n_pre )) ” 
  &&  “ (PrefixGreedyState input sorted i kept spent ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i a_pre i 0 n_pre sorted )
.

Definition solver_partial_solve_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (spent: Z) (kept: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((kept + 1 ) <= (Znth i sorted 0))) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullPreparationSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre)))) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= kept)) (PreH14 : (kept <= i)) (PreH15 : (0 <= spent)) (PreH16 : (spent <= (i * n_pre ))) (PreH17 : (PrefixGreedyState input sorted i kept spent )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  “ ((kept + 1 ) <= (Znth i sorted 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullPreparationSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= n_pre))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= kept) ” 
  &&  “ (kept <= i) ” 
  &&  “ (0 <= spent) ” 
  &&  “ (spent <= (i * n_pre )) ” 
  &&  “ (PrefixGreedyState input sorted i kept spent ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i a_pre i 0 n_pre sorted )
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.

End VC_Correct.
