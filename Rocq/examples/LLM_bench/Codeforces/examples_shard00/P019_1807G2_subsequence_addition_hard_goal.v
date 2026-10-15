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
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P019_1807G2_subsequence_addition_hard_lib.
Local Open Scope sac.

(*----- Function cmp_int -----*)

(*----- Function solver -----*)

Definition solver_safety_wit_1 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (Permutation input sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (FullDecisionSpecBridge input sorted )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (Permutation input sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (FullDecisionSpecBridge input sorted )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : ((Znth 0 sorted 0) <> 1)) (PreH2 : (Permutation input sorted )) (PreH3 : (increasing sorted )) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : ((Znth 0 sorted 0) = 1)) (PreH2 : (Permutation input sorted )) (PreH3 : (increasing sorted )) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  ((( &( "sum" ) )) # Int64  |->_)
  **  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_5 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : ((Znth 0 sorted 0) = 1)) (PreH2 : (Permutation input sorted )) (PreH3 : (increasing sorted )) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int64  |-> 1)
  **  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_6 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((Znth i sorted 0) > sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullDecisionSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted i sum )) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_7 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((Znth i sorted 0) <= sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullDecisionSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted i sum )) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
|--
  “ ((sum + (Znth i sorted 0) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (sum + (Znth i sorted 0) )) ”
.

Definition solver_safety_wit_8 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((Znth i sorted 0) <= sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullDecisionSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted i sum )) ,
  (IntArray.full a_pre n_pre sorted )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int64  |-> (sum + (Znth i sorted 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_9 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullDecisionSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= sum)) (PreH13 : (sum <= (200000 * i ))) (PreH14 : (PrefixAdditionState sorted i sum )) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int64  |-> sum)
  **  (IntArray.full a_pre n_pre sorted )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (PreH1 : ((Znth 0 sorted_2 0) = 1)) (PreH2 : (Permutation input sorted_2 )) (PreH3 : (increasing sorted_2 )) (PreH4 : ((Zlength (sorted_2)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted_2 )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  (IntArray.full a_pre n_pre sorted_2 )
|--
  EX (sorted: (@list Z)) ,
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullDecisionSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (200000 * 1 )) ” 
  &&  “ (PrefixAdditionState sorted 1 1 ) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (PreH1 : ((Znth 0 sorted_2 0) = 1)) (PreH2 : (Permutation input sorted_2 )) (PreH3 : (increasing sorted_2 )) (PreH4 : ((Zlength (sorted_2)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted_2 )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  TT && emp 
|--
  “ (PrefixAdditionState sorted_2 1 1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 200000))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (PreH1 : ((Znth 0 sorted_2 0) = 1)) (PreH2 : (Permutation input sorted_2 )) (PreH3 : (increasing sorted_2 )) (PreH4 : ((Zlength (sorted_2)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted_2 )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  (PrefixAdditionState sorted_2 1 1 )
.

Definition solver_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (input: (@list Z)) (sorted_2: (@list Z)) (PreH1 : ((Znth 0 sorted_2 0) = 1)) (PreH2 : (Permutation input sorted_2 )) (PreH3 : (increasing sorted_2 )) (PreH4 : ((Zlength (sorted_2)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted_2 )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 200000)))
.

Definition solver_entail_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((Znth i sorted_2 0) <= sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullDecisionSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted_2 i sum )) ,
  (IntArray.full a_pre n_pre sorted_2 )
|--
  EX (sorted: (@list Z)) ,
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullDecisionSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000))) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (1 <= (sum + (Znth i sorted_2 0) )) ” 
  &&  “ ((sum + (Znth i sorted_2 0) ) <= (200000 * (i + 1 ) )) ” 
  &&  “ (PrefixAdditionState sorted (i + 1 ) (sum + (Znth i sorted_2 0) ) ) ”
  &&  (IntArray.full a_pre n_pre sorted )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((Znth i sorted_2 0) <= sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullDecisionSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted_2 i sum )) ,
  TT && emp 
|--
  “ (PrefixAdditionState sorted_2 (i + 1 ) (sum + (Znth i sorted_2 0) ) ) ”
  &&  emp
).

Definition solver_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted_2: (@list Z)) (PreH1 : ((Znth i sorted_2 0) <= sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted_2)) = n_pre)) (PreH7 : (Permutation input sorted_2 )) (PreH8 : (increasing sorted_2 )) (PreH9 : (FullDecisionSpecBridge input sorted_2 )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted_2 0)) /\ ((Znth k sorted_2 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted_2 i sum )) ,
  (PrefixAdditionState sorted_2 (i + 1 ) (sum + (Znth i sorted_2 0) ) )
.

Definition solver_return_wit_1 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullDecisionSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= sum)) (PreH13 : (sum <= (200000 * i ))) (PreH14 : (PrefixAdditionState sorted i sum )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  EX (post: (@list Z)) ,
  “ (Spec input 1 ) ”
  &&  (IntArray.full a_pre n_pre post )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullDecisionSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= sum)) (PreH13 : (sum <= (200000 * i ))) (PreH14 : (PrefixAdditionState sorted i sum )) ,
  TT && emp 
|--
  “ (Spec input 1 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullDecisionSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= sum)) (PreH13 : (sum <= (200000 * i ))) (PreH14 : (PrefixAdditionState sorted i sum )) ,
  (Spec input 1 )
.

Definition solver_return_wit_2 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((Znth i sorted 0) > sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullDecisionSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted i sum )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  EX (post: (@list Z)) ,
  “ (Spec input 0 ) ”
  &&  (IntArray.full a_pre n_pre post )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((Znth i sorted 0) > sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullDecisionSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted i sum )) ,
  TT && emp 
|--
  “ (Spec input 0 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((Znth i sorted 0) > sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullDecisionSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted i sum )) ,
  (Spec input 0 )
.

Definition solver_return_wit_3 := 
(
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : ((Znth 0 sorted 0) <> 1)) (PreH2 : (Permutation input sorted )) (PreH3 : (increasing sorted )) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  (IntArray.full a_pre n_pre sorted )
|--
  EX (post: (@list Z)) ,
  “ (Spec input 0 ) ”
  &&  (IntArray.full a_pre n_pre post )
) \/
(
forall (n_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : ((Znth 0 sorted 0) <> 1)) (PreH2 : (Permutation input sorted )) (PreH3 : (increasing sorted )) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  TT && emp 
|--
  “ (Spec input 0 ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 := 
forall (n_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : ((Znth 0 sorted 0) <> 1)) (PreH2 : (Permutation input sorted )) (PreH3 : (increasing sorted )) (PreH4 : ((Zlength (sorted)) = n_pre)) (PreH5 : (FullDecisionSpecBridge input sorted )) (PreH6 : (n_pre = (Zlength (input)))) (PreH7 : (1 <= (Zlength (input)))) (PreH8 : ((Zlength (input)) <= 200000)) (PreH9 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  (Spec input 0 )
.

Definition solver_partial_solve_wit_1_pure := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre input )
|--
  “ (n_pre = (Zlength (input))) ”
.

Definition solver_partial_solve_wit_1_aux := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (PreH1 : (n_pre = (Zlength (input)))) (PreH2 : (1 <= (Zlength (input)))) (PreH3 : ((Zlength (input)) <= 200000)) (PreH4 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  (IntArray.full a_pre n_pre input )
|--
  “ (n_pre = (Zlength (input))) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= (Zlength (input))) ” 
  &&  “ ((Zlength (input)) <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000))) ”
  &&  (IntArray.full a_pre n_pre input )
.

Definition solver_partial_solve_wit_1 := solver_partial_solve_wit_1_pure -> solver_partial_solve_wit_1_aux.

Definition solver_partial_solve_wit_2 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sorted: (@list Z)) (PreH1 : (Permutation input sorted )) (PreH2 : (increasing sorted )) (PreH3 : ((Zlength (sorted)) = n_pre)) (PreH4 : (FullDecisionSpecBridge input sorted )) (PreH5 : (n_pre = (Zlength (input)))) (PreH6 : (1 <= (Zlength (input)))) (PreH7 : ((Zlength (input)) <= 200000)) (PreH8 : forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000)))) ,
  (IntArray.full a_pre n_pre sorted )
|--
  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (FullDecisionSpecBridge input sorted ) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= (Zlength (input))) ” 
  &&  “ ((Zlength (input)) <= 200000) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (Zlength (input)))) -> ((1 <= (Znth i input 0)) /\ ((Znth i input 0) <= 200000))) ”
  &&  (((a_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 sorted 0))
  **  (IntArray.missing_i a_pre 0 0 n_pre sorted )
.

Definition solver_partial_solve_wit_3 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (n_pre = (Zlength (input)))) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : ((Zlength (sorted)) = n_pre)) (PreH6 : (Permutation input sorted )) (PreH7 : (increasing sorted )) (PreH8 : (FullDecisionSpecBridge input sorted )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= sum)) (PreH13 : (sum <= (200000 * i ))) (PreH14 : (PrefixAdditionState sorted i sum )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullDecisionSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= sum) ” 
  &&  “ (sum <= (200000 * i )) ” 
  &&  “ (PrefixAdditionState sorted i sum ) ”
  &&  (((a_pre + (i * sizeof(INT)))) # Int  |-> (Znth i sorted 0))
  **  (IntArray.missing_i a_pre i 0 n_pre sorted )
.

Definition solver_partial_solve_wit_4 := 
forall (n_pre: Z) (a_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (sorted: (@list Z)) (PreH1 : ((Znth i sorted 0) <= sum)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre = (Zlength (input)))) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : ((Zlength (sorted)) = n_pre)) (PreH7 : (Permutation input sorted )) (PreH8 : (increasing sorted )) (PreH9 : (FullDecisionSpecBridge input sorted )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000)))) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= sum)) (PreH14 : (sum <= (200000 * i ))) (PreH15 : (PrefixAdditionState sorted i sum )) ,
  (IntArray.full a_pre n_pre sorted )
|--
  “ ((Znth i sorted 0) <= sum) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre = (Zlength (input))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 200000) ” 
  &&  “ ((Zlength (sorted)) = n_pre) ” 
  &&  “ (Permutation input sorted ) ” 
  &&  “ (increasing sorted ) ” 
  &&  “ (FullDecisionSpecBridge input sorted ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k sorted 0)) /\ ((Znth k sorted 0) <= 200000))) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= sum) ” 
  &&  “ (sum <= (200000 * i )) ” 
  &&  “ (PrefixAdditionState sorted i sum ) ”
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
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_partial_solve_wit_1_pure : solver_partial_solve_wit_1_pure.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.

End VC_Correct.
