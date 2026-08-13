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
Require Import SimpleC.EE.LLM_bench.Algorithms.quicksort_hoare_swap_index.quicksort_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function partition -----*)

Definition partition_safety_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (pivot = (Znth low_pre l 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n)) (PreH7 : (low_pre <= i)) (PreH8 : (i <= j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l (replace_Znth (i) (pivot) (l1)) )) (PreH11 : (same_outside_range l l1 low_pre high_pre )) (PreH12 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH13 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n l1 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_safety_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) > pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (Permutation l (replace_Znth (i) (pivot) (l1)) )) (PreH13 : (same_outside_range l l1 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH15 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition partition_safety_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (Permutation l (replace_Znth (i) (pivot) (l1)) )) (PreH13 : (same_outside_range l l1 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH15 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n l1 )
|--
  “ False ”
.

Definition partition_safety_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : ((Znth j l1 0) <= pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (i) (pivot) (l1)) )) (PreH14 : (same_outside_range l l1 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ False ”
.

Definition partition_safety_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth j l1 0) <= pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (i) (pivot) (l1)) )) (PreH14 : (same_outside_range l l1 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n (replace_Znth (i) ((Znth j l1 0)) (l1)) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_safety_wit_6 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth i l1 0) <= pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (Permutation l (replace_Znth (j) (pivot) (l1)) )) (PreH13 : (same_outside_range l l1 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH15 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_safety_wit_7 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (Permutation l (replace_Znth (j) (pivot) (l1)) )) (PreH13 : (same_outside_range l l1 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH15 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n l1 )
|--
  “ False ”
.

Definition partition_safety_wit_8 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : ((Znth i l1 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (j) (pivot) (l1)) )) (PreH14 : (same_outside_range l l1 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ False ”
.

Definition partition_safety_wit_9 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth i l1 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (j) (pivot) (l1)) )) (PreH14 : (same_outside_range l l1 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n (replace_Znth (j) ((Znth i l1 0)) (l1)) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition partition_entail_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 50000)) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n)) ,
  ((( &( "j" ) )) # Int  |-> high_pre)
  **  ((( &( "i" ) )) # Int  |-> low_pre)
  **  (IntArray.full arr_pre n l )
  **  ((( &( "pivot" ) )) # Int  |-> (Znth low_pre l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
|--
  EX (l1: (@list Z))  (j: Z)  (i: Z)  (pivot: Z) ,
  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (i) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n)) (PreH2 : (1 <= n)) (PreH3 : (n <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n)) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((high_pre < k_2) /\ (k_2 <= high_pre)) -> ((Znth low_pre l 0) <= (Znth k_2 l 0))) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < low_pre)) -> ((Znth k l 0) <= (Znth low_pre l 0))) ” 
  &&  “ (same_outside_range l l low_pre high_pre ) ” 
  &&  “ (Permutation l (replace_Znth (low_pre) ((Znth low_pre l 0)) (l)) ) ”
  &&  emp
).

Definition partition_entail_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n)) (PreH2 : (1 <= n)) (PreH3 : (n <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n)) ,
  forall (k_2: Z) , (((high_pre < k_2) /\ (k_2 <= high_pre)) -> ((Znth low_pre l 0) <= (Znth k_2 l 0)))
.

Definition partition_entail_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n)) (PreH2 : (1 <= n)) (PreH3 : (n <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n)) ,
  forall (k: Z) , (((low_pre <= k) /\ (k < low_pre)) -> ((Znth k l 0) <= (Znth low_pre l 0)))
.

Definition partition_entail_wit_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n)) (PreH2 : (1 <= n)) (PreH3 : (n <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n)) ,
  (same_outside_range l l low_pre high_pre )
.

Definition partition_entail_wit_1_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n)) (PreH2 : (1 <= n)) (PreH3 : (n <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n)) ,
  (Permutation l (replace_Znth (low_pre) ((Znth low_pre l 0)) (l)) )
.

Definition partition_entail_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : (pivot_2 = (Znth low_pre l 0))) (PreH2 : (1 <= n)) (PreH3 : (n <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n)) (PreH7 : (low_pre <= i_2)) (PreH8 : (i_2 <= j_2)) (PreH9 : (j_2 <= high_pre)) (PreH10 : (Permutation l (replace_Znth (i_2) (pivot_2) (l1_2)) )) (PreH11 : (same_outside_range l l1_2 low_pre high_pre )) (PreH12 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH13 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> j_2)
  **  (IntArray.full arr_pre n l1_2 )
|--
  EX (l1: (@list Z))  (j: Z)  (i: Z)  (pivot: Z) ,
  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (i) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n l1 )
.

Definition partition_entail_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Znth j_2 l1_2 0) > pivot_2)) (PreH2 : (i_2 < j_2)) (PreH3 : (pivot_2 = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i_2)) (PreH10 : (i_2 <= j_2)) (PreH11 : (j_2 <= high_pre)) (PreH12 : (Permutation l (replace_Znth (i_2) (pivot_2) (l1_2)) )) (PreH13 : (same_outside_range l l1_2 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i_2)) -> ((Znth k l1_2 0) <= pivot_2))) (PreH15 : forall (k_2: Z) , (((j_2 < k_2) /\ (k_2 <= high_pre)) -> (pivot_2 <= (Znth k_2 l1_2 0)))) ,
  (IntArray.full arr_pre n l1_2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> (j_2 - 1 ))
|--
  EX (l1: (@list Z))  (j: Z)  (i: Z)  (pivot: Z) ,
  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (i) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n l1 )
.

Definition partition_entail_wit_4 := 
(
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : (i_2 < j_2)) (PreH2 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH3 : (i_2 < j_2)) (PreH4 : (pivot_2 = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i_2)) (PreH11 : (i_2 <= j_2)) (PreH12 : (j_2 <= high_pre)) (PreH13 : (Permutation l (replace_Znth (i_2) (pivot_2) (l1_2)) )) (PreH14 : (same_outside_range l l1_2 low_pre high_pre )) (PreH15 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH16 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  (IntArray.full arr_pre n (replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_2)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j_2)
|--
  EX (l1: (@list Z))  (j: Z)  (i: Z)  (pivot: Z) ,
  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (j) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (i_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  TT && emp 
|--
  “ forall (k_2: Z) , (((j_2 < k_2) /\ (k_2 <= high_pre)) -> ((Znth low_pre l 0) <= (Znth k_2 (replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)) 0))) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < (i_2 + 1 ))) -> ((Znth k (replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)) 0) <= (Znth low_pre l 0))) ” 
  &&  “ (same_outside_range l (replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)) low_pre high_pre ) ” 
  &&  “ (Permutation l (replace_Znth (j_2) (pivot_2) ((replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)))) ) ”
  &&  emp
).

Definition partition_entail_wit_4_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (i_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  forall (k_2: Z) , (((j_2 < k_2) /\ (k_2 <= high_pre)) -> ((Znth low_pre l 0) <= (Znth k_2 (replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)) 0)))
.

Definition partition_entail_wit_4_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (i_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  forall (k: Z) , (((low_pre <= k) /\ (k < (i_2 + 1 ))) -> ((Znth k (replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)) 0) <= (Znth low_pre l 0)))
.

Definition partition_entail_wit_4_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (i_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  (same_outside_range l (replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)) low_pre high_pre )
.

Definition partition_entail_wit_4_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (i_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  (Permutation l (replace_Znth (j_2) (pivot_2) ((replace_Znth (i_2) ((Znth j_2 l1_2 0)) (l1_2)))) )
.

Definition partition_entail_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Znth i_2 l1_2 0) <= pivot_2)) (PreH2 : (i_2 < j_2)) (PreH3 : (pivot_2 = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i_2)) (PreH10 : (i_2 <= j_2)) (PreH11 : (j_2 <= high_pre)) (PreH12 : (Permutation l (replace_Znth (j_2) (pivot_2) (l1_2)) )) (PreH13 : (same_outside_range l l1_2 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i_2)) -> ((Znth k l1_2 0) <= pivot_2))) (PreH15 : forall (k_2: Z) , (((j_2 < k_2) /\ (k_2 <= high_pre)) -> (pivot_2 <= (Znth k_2 l1_2 0)))) ,
  (IntArray.full arr_pre n l1_2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_2)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j_2)
|--
  EX (l1: (@list Z))  (j: Z)  (i: Z)  (pivot: Z) ,
  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (j) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n l1 )
.

Definition partition_entail_wit_6 := 
(
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : (i_2 < j_2)) (PreH2 : ((Znth i_2 l1_2 0) > pivot_2)) (PreH3 : (i_2 < j_2)) (PreH4 : (pivot_2 = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i_2)) (PreH11 : (i_2 <= j_2)) (PreH12 : (j_2 <= high_pre)) (PreH13 : (Permutation l (replace_Znth (j_2) (pivot_2) (l1_2)) )) (PreH14 : (same_outside_range l l1_2 low_pre high_pre )) (PreH15 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH16 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  (IntArray.full arr_pre n (replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> (j_2 - 1 ))
|--
  EX (l1: (@list Z))  (j: Z)  (i: Z)  (pivot: Z) ,
  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (i) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth i_2 l1_2 0) > pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (j_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  TT && emp 
|--
  “ forall (k_2: Z) , ((((j_2 - 1 ) < k_2) /\ (k_2 <= high_pre)) -> ((Znth low_pre l 0) <= (Znth k_2 (replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)) 0))) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i_2)) -> ((Znth k (replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)) 0) <= (Znth low_pre l 0))) ” 
  &&  “ (same_outside_range l (replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)) low_pre high_pre ) ” 
  &&  “ (Permutation l (replace_Znth (i_2) (pivot_2) ((replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)))) ) ”
  &&  emp
).

Definition partition_entail_wit_6_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth i_2 l1_2 0) > pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (j_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  forall (k_2: Z) , ((((j_2 - 1 ) < k_2) /\ (k_2 <= high_pre)) -> ((Znth low_pre l 0) <= (Znth k_2 (replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)) 0)))
.

Definition partition_entail_wit_6_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth i_2 l1_2 0) > pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (j_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  forall (k: Z) , (((low_pre <= k) /\ (k < i_2)) -> ((Znth k (replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)) 0) <= (Znth low_pre l 0)))
.

Definition partition_entail_wit_6_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth i_2 l1_2 0) > pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (j_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  (same_outside_range l (replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)) low_pre high_pre )
.

Definition partition_entail_wit_6_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)))) = n)) (PreH2 : (i_2 < j_2)) (PreH3 : ((Znth i_2 l1_2 0) > pivot_2)) (PreH4 : (i_2 < j_2)) (PreH5 : (pivot_2 = (Znth low_pre l 0))) (PreH6 : (1 <= n)) (PreH7 : (n <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n)) (PreH11 : (low_pre <= i_2)) (PreH12 : (i_2 <= j_2)) (PreH13 : (j_2 <= high_pre)) (PreH14 : (Permutation l (replace_Znth (j_2) (pivot_2) (l1_2)) )) (PreH15 : (same_outside_range l l1_2 low_pre high_pre )) (PreH16 : forall (k_3: Z) , (((low_pre <= k_3) /\ (k_3 < i_2)) -> ((Znth k_3 l1_2 0) <= pivot_2))) (PreH17 : forall (k_4: Z) , (((j_2 < k_4) /\ (k_4 <= high_pre)) -> (pivot_2 <= (Znth k_4 l1_2 0)))) ,
  (Permutation l (replace_Znth (i_2) (pivot_2) ((replace_Znth (j_2) ((Znth i_2 l1_2 0)) (l1_2)))) )
.

Definition partition_return_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (Permutation l (replace_Znth (i) (pivot) (l1_2)) )) (PreH13 : (same_outside_range l l1_2 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) (PreH15 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) ,
  (IntArray.full arr_pre n (replace_Znth (i) (pivot) (l1_2)) )
|--
  EX (l1: (@list Z)) ,
  “ (low_pre <= i) ” 
  &&  “ (i <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ (partitioned_at l1 low_pre high_pre i ) ”
  &&  (IntArray.full arr_pre n l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (i) (pivot) (l1_2)))) = n)) (PreH2 : (i >= j)) (PreH3 : (i >= j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (i) (pivot) (l1_2)) )) (PreH14 : (same_outside_range l l1_2 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) ,
  TT && emp 
|--
  “ (partitioned_at (replace_Znth (i) (pivot) (l1_2)) low_pre high_pre i ) ” 
  &&  “ (same_outside_range l (replace_Znth (i) (pivot) (l1_2)) low_pre high_pre ) ”
  &&  emp
).

Definition partition_return_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (i) (pivot) (l1_2)))) = n)) (PreH2 : (i >= j)) (PreH3 : (i >= j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (i) (pivot) (l1_2)) )) (PreH14 : (same_outside_range l l1_2 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) ,
  (partitioned_at (replace_Znth (i) (pivot) (l1_2)) low_pre high_pre i )
.

Definition partition_return_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (i) (pivot) (l1_2)))) = n)) (PreH2 : (i >= j)) (PreH3 : (i >= j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (i) (pivot) (l1_2)) )) (PreH14 : (same_outside_range l l1_2 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) ,
  (same_outside_range l (replace_Znth (i) (pivot) (l1_2)) low_pre high_pre )
.

Definition partition_return_wit_2 := 
(
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (Permutation l (replace_Znth (j) (pivot) (l1_2)) )) (PreH13 : (same_outside_range l l1_2 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) (PreH15 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) ,
  (IntArray.full arr_pre n (replace_Znth (i) (pivot) (l1_2)) )
|--
  EX (l1: (@list Z)) ,
  “ (low_pre <= i) ” 
  &&  “ (i <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ (partitioned_at l1 low_pre high_pre i ) ”
  &&  (IntArray.full arr_pre n l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (i) (pivot) (l1_2)))) = n)) (PreH2 : (i >= j)) (PreH3 : (i >= j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (j) (pivot) (l1_2)) )) (PreH14 : (same_outside_range l l1_2 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) ,
  TT && emp 
|--
  “ (partitioned_at (replace_Znth (i) (pivot) (l1_2)) low_pre high_pre i ) ” 
  &&  “ (same_outside_range l (replace_Znth (i) (pivot) (l1_2)) low_pre high_pre ) ” 
  &&  “ (Permutation l (replace_Znth (i) (pivot) (l1_2)) ) ”
  &&  emp
).

Definition partition_return_wit_2_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (i) (pivot) (l1_2)))) = n)) (PreH2 : (i >= j)) (PreH3 : (i >= j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (j) (pivot) (l1_2)) )) (PreH14 : (same_outside_range l l1_2 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) ,
  (partitioned_at (replace_Znth (i) (pivot) (l1_2)) low_pre high_pre i )
.

Definition partition_return_wit_2_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (i) (pivot) (l1_2)))) = n)) (PreH2 : (i >= j)) (PreH3 : (i >= j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (j) (pivot) (l1_2)) )) (PreH14 : (same_outside_range l l1_2 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) ,
  (same_outside_range l (replace_Znth (i) (pivot) (l1_2)) low_pre high_pre )
.

Definition partition_return_wit_2_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (i) (pivot) (l1_2)))) = n)) (PreH2 : (i >= j)) (PreH3 : (i >= j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (j) (pivot) (l1_2)) )) (PreH14 : (same_outside_range l l1_2 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1_2 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1_2 0)))) ,
  (Permutation l (replace_Znth (i) (pivot) (l1_2)) )
.

Definition partition_partial_solve_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : (1 <= n)) (PreH2 : (n <= 50000)) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n)) ,
  (IntArray.full arr_pre n l )
|--
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ”
  &&  (((arr_pre + (low_pre * sizeof(INT)))) # Int  |-> (Znth low_pre l 0))
  **  (IntArray.missing_i arr_pre low_pre 0 n l )
.

Definition partition_partial_solve_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (pivot = (Znth low_pre l 0))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n)) (PreH8 : (low_pre <= i)) (PreH9 : (i <= j)) (PreH10 : (j <= high_pre)) (PreH11 : (Permutation l (replace_Znth (i) (pivot) (l1)) )) (PreH12 : (same_outside_range l l1 low_pre high_pre )) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (i < j) ” 
  &&  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (i) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l1 0))
  **  (IntArray.missing_i arr_pre j 0 n l1 )
.

Definition partition_partial_solve_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth j l1 0) <= pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (i) (pivot) (l1)) )) (PreH14 : (same_outside_range l l1 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (i < j) ” 
  &&  “ ((Znth j l1 0) <= pivot) ” 
  &&  “ (i < j) ” 
  &&  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (i) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l1 0))
  **  (IntArray.missing_i arr_pre j 0 n l1 )
.

Definition partition_partial_solve_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth j l1 0) <= pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (i) (pivot) (l1)) )) (PreH14 : (same_outside_range l l1 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (i < j) ” 
  &&  “ ((Znth j l1 0) <= pivot) ” 
  &&  “ (i < j) ” 
  &&  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (i) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre i 0 n l1 )
.

Definition partition_partial_solve_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (pivot = (Znth low_pre l 0))) (PreH3 : (1 <= n)) (PreH4 : (n <= 50000)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n)) (PreH8 : (low_pre <= i)) (PreH9 : (i <= j)) (PreH10 : (j <= high_pre)) (PreH11 : (Permutation l (replace_Znth (j) (pivot) (l1)) )) (PreH12 : (same_outside_range l l1 low_pre high_pre )) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (i < j) ” 
  &&  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (j) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l1 0))
  **  (IntArray.missing_i arr_pre i 0 n l1 )
.

Definition partition_partial_solve_wit_6 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth i l1 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (j) (pivot) (l1)) )) (PreH14 : (same_outside_range l l1 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (i < j) ” 
  &&  “ ((Znth i l1 0) > pivot) ” 
  &&  “ (i < j) ” 
  &&  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (j) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l1 0))
  **  (IntArray.missing_i arr_pre i 0 n l1 )
.

Definition partition_partial_solve_wit_7 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth i l1 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth low_pre l 0))) (PreH5 : (1 <= n)) (PreH6 : (n <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (Permutation l (replace_Znth (j) (pivot) (l1)) )) (PreH14 : (same_outside_range l l1 low_pre high_pre )) (PreH15 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH16 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (i < j) ” 
  &&  “ ((Znth i l1 0) > pivot) ” 
  &&  “ (i < j) ” 
  &&  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (j) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre j 0 n l1 )
.

Definition partition_partial_solve_wit_8 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (Permutation l (replace_Znth (i) (pivot) (l1)) )) (PreH13 : (same_outside_range l l1 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH15 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (i >= j) ” 
  &&  “ (i >= j) ” 
  &&  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (i) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre i 0 n l1 )
.

Definition partition_partial_solve_wit_9 := 
forall (high_pre: Z) (low_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth low_pre l 0))) (PreH4 : (1 <= n)) (PreH5 : (n <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (Permutation l (replace_Znth (j) (pivot) (l1)) )) (PreH13 : (same_outside_range l l1 low_pre high_pre )) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot))) (PreH15 : forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (i >= j) ” 
  &&  “ (i >= j) ” 
  &&  “ (pivot = (Znth low_pre l 0)) ” 
  &&  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l (replace_Znth (j) (pivot) (l1)) ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k < i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((j < k_2) /\ (k_2 <= high_pre)) -> (pivot <= (Znth k_2 l1 0))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre i 0 n l1 )
.

(*----- Function quicksort_range -----*)

Definition quicksort_range_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (0 <= n)) (PreH8 : (n <= 50000)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quicksort_range_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (0 <= n)) (PreH8 : (n <= 50000)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_range_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (0 <= n)) (PreH12 : (n <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_range_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (0 <= n)) (PreH12 : (n <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_range_safety_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (0 <= n)) (PreH9 : (n <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= right_pre)) (PreH12 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_range_safety_wit_6 := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (0 <= n)) (PreH9 : (n <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= right_pre)) (PreH12 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_range_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (Permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (Permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (0 <= n)) (PreH15 : (n <= 50000)) (PreH16 : (0 <= left_pre)) (PreH17 : (left_pre <= right_pre)) (PreH18 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1_4 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : ((Zlength (l1_4)) = n)) (PreH2 : (Permutation l1_3 l1_4 )) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3 )) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2 )) (PreH13 : (same_outside_range l l1_2 left_pre right_pre )) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH15 : (0 <= n)) (PreH16 : (n <= 50000)) (PreH17 : (0 <= left_pre)) (PreH18 : (left_pre <= right_pre)) (PreH19 : (right_pre < n)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_4 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_4 left_pre right_pre ) ” 
  &&  “ (Permutation l l1_4 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : ((Zlength (l1_4)) = n)) (PreH2 : (Permutation l1_3 l1_4 )) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3 )) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2 )) (PreH13 : (same_outside_range l l1_2 left_pre right_pre )) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH15 : (0 <= n)) (PreH16 : (n <= 50000)) (PreH17 : (0 <= left_pre)) (PreH18 : (left_pre <= right_pre)) (PreH19 : (right_pre < n)) ,
  (range_nondecreasing l1_4 left_pre right_pre )
.

Definition quicksort_range_return_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : ((Zlength (l1_4)) = n)) (PreH2 : (Permutation l1_3 l1_4 )) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3 )) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2 )) (PreH13 : (same_outside_range l l1_2 left_pre right_pre )) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH15 : (0 <= n)) (PreH16 : (n <= 50000)) (PreH17 : (0 <= left_pre)) (PreH18 : (left_pre <= right_pre)) (PreH19 : (right_pre < n)) ,
  (same_outside_range l l1_4 left_pre right_pre )
.

Definition quicksort_range_return_wit_1_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : ((Zlength (l1_4)) = n)) (PreH2 : (Permutation l1_3 l1_4 )) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3 )) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2 )) (PreH13 : (same_outside_range l l1_2 left_pre right_pre )) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH15 : (0 <= n)) (PreH16 : (n <= 50000)) (PreH17 : (0 <= left_pre)) (PreH18 : (left_pre <= right_pre)) (PreH19 : (right_pre < n)) ,
  (Permutation l l1_4 )
.

Definition quicksort_range_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (Permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (0 <= n)) (PreH12 : (n <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1_3 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (0 <= n)) (PreH13 : (n <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre < n)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_3 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_3 left_pre right_pre ) ” 
  &&  “ (Permutation l l1_3 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (0 <= n)) (PreH13 : (n <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre < n)) ,
  (range_nondecreasing l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_2_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (0 <= n)) (PreH13 : (n <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre < n)) ,
  (same_outside_range l l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_2_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (0 <= n)) (PreH13 : (n <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre < n)) ,
  (Permutation l l1_3 )
.

Definition quicksort_range_return_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (0 <= n)) (PreH12 : (n <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1_3 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3 )) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (0 <= n)) (PreH13 : (n <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre < n)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_3 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_3 left_pre right_pre ) ” 
  &&  “ (Permutation l l1_3 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3 )) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (0 <= n)) (PreH13 : (n <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre < n)) ,
  (range_nondecreasing l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_3_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3 )) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (0 <= n)) (PreH13 : (n <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre < n)) ,
  (same_outside_range l l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_3_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3 )) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (0 <= n)) (PreH13 : (n <= 50000)) (PreH14 : (0 <= left_pre)) (PreH15 : (left_pre <= right_pre)) (PreH16 : (right_pre < n)) ,
  (Permutation l l1_3 )
.

Definition quicksort_range_return_wit_4 := 
(
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1_2 )) (PreH6 : (same_outside_range l l1_2 left_pre right_pre )) (PreH7 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH8 : (0 <= n)) (PreH9 : (n <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= right_pre)) (PreH12 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l1_2)) = n)) (PreH2 : (retval >= right_pre)) (PreH3 : (retval <= left_pre)) (PreH4 : (left_pre <= retval)) (PreH5 : (retval <= right_pre)) (PreH6 : (Permutation l l1_2 )) (PreH7 : (same_outside_range l l1_2 left_pre right_pre )) (PreH8 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH9 : (0 <= n)) (PreH10 : (n <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : (left_pre <= right_pre)) (PreH13 : (right_pre < n)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_2 left_pre right_pre ) ”
  &&  emp
).

Definition quicksort_range_return_wit_4_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (PreH1 : ((Zlength (l1_2)) = n)) (PreH2 : (retval >= right_pre)) (PreH3 : (retval <= left_pre)) (PreH4 : (left_pre <= retval)) (PreH5 : (retval <= right_pre)) (PreH6 : (Permutation l l1_2 )) (PreH7 : (same_outside_range l l1_2 left_pre right_pre )) (PreH8 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH9 : (0 <= n)) (PreH10 : (n <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : (left_pre <= right_pre)) (PreH13 : (right_pre < n)) ,
  (range_nondecreasing l1_2 left_pre right_pre )
.

Definition quicksort_range_partial_solve_wit_1_pure := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= 50000)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre <= right_pre)) (PreH5 : (right_pre < n)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full arr_pre n l )
|--
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ”
.

Definition quicksort_range_partial_solve_wit_1_aux := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (PreH1 : (0 <= n)) (PreH2 : (n <= 50000)) (PreH3 : (0 <= left_pre)) (PreH4 : (left_pre <= right_pre)) (PreH5 : (right_pre < n)) ,
  (IntArray.full arr_pre n l )
|--
  “ (1 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ”
  &&  (IntArray.full arr_pre n l )
.

Definition quicksort_range_partial_solve_wit_1 := quicksort_range_partial_solve_wit_1_pure -> quicksort_range_partial_solve_wit_1_aux.

Definition quicksort_range_partial_solve_wit_2_pure := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (0 <= n)) (PreH8 : (n <= 50000)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n) ”
.

Definition quicksort_range_partial_solve_wit_2_aux := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (0 <= n)) (PreH8 : (n <= 50000)) (PreH9 : (0 <= left_pre)) (PreH10 : (left_pre <= right_pre)) (PreH11 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (partitioned_at l1 left_pre right_pre retval ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ”
  &&  (IntArray.full arr_pre n l1 )
.

Definition quicksort_range_partial_solve_wit_2 := quicksort_range_partial_solve_wit_2_pure -> quicksort_range_partial_solve_wit_2_aux.

Definition quicksort_range_partial_solve_wit_3_pure := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (0 <= n)) (PreH12 : (n <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= right_pre) ” 
  &&  “ (right_pre < n) ”
.

Definition quicksort_range_partial_solve_wit_3_aux := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (0 <= n)) (PreH12 : (n <= 50000)) (PreH13 : (0 <= left_pre)) (PreH14 : (left_pre <= right_pre)) (PreH15 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1_2 )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (Permutation l1 l1_2 ) ” 
  &&  “ (same_outside_range l1 l1_2 left_pre (retval - 1 ) ) ” 
  &&  “ (range_nondecreasing l1_2 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (partitioned_at l1 left_pre right_pre retval ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ”
  &&  (IntArray.full arr_pre n l1_2 )
.

Definition quicksort_range_partial_solve_wit_3 := quicksort_range_partial_solve_wit_3_pure -> quicksort_range_partial_solve_wit_3_aux.

Definition quicksort_range_partial_solve_wit_4_pure := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (0 <= n)) (PreH9 : (n <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= right_pre)) (PreH12 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= right_pre) ” 
  &&  “ (right_pre < n) ”
.

Definition quicksort_range_partial_solve_wit_4_aux := 
forall (right_pre: Z) (left_pre: Z) (arr_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (0 <= n)) (PreH9 : (n <= 50000)) (PreH10 : (0 <= left_pre)) (PreH11 : (left_pre <= right_pre)) (PreH12 : (right_pre < n)) ,
  (IntArray.full arr_pre n l1 )
|--
  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= right_pre) ” 
  &&  “ (right_pre < n) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (partitioned_at l1 left_pre right_pre retval ) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n) ”
  &&  (IntArray.full arr_pre n l1 )
.

Definition quicksort_range_partial_solve_wit_4 := quicksort_range_partial_solve_wit_4_pure -> quicksort_range_partial_solve_wit_4_aux.

(*----- Function quicksort -----*)

Definition quicksort_safety_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_safety_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition quicksort_safety_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_safety_wit_4 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_return_wit_1 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : (Permutation l l1_2 )) (PreH2 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH3 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH4 : (n_pre > 0)) (PreH5 : (0 <= n_pre)) (PreH6 : (n_pre <= 50000)) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : ((Zlength (l1_2)) = n_pre)) (PreH2 : (Permutation l l1_2 )) (PreH3 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH4 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ (increasing l1_2 ) ”
  &&  emp
).

Definition quicksort_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : ((Zlength (l1_2)) = n_pre)) (PreH2 : (Permutation l l1_2 )) (PreH3 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH4 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH5 : (n_pre > 0)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) ,
  (increasing l1_2 )
.

Definition quicksort_return_wit_2 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (n_pre <= 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ (increasing l ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition quicksort_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (n_pre <= 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  (increasing l )
.

Definition quicksort_return_wit_2_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (n_pre <= 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  (Permutation l l )
.

Definition quicksort_partial_solve_wit_1_pure := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ”
.

Definition quicksort_partial_solve_wit_1_aux := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition quicksort_partial_solve_wit_1 := quicksort_partial_solve_wit_1_pure -> quicksort_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_partition_safety_wit_1 : partition_safety_wit_1.
Axiom proof_of_partition_safety_wit_2 : partition_safety_wit_2.
Axiom proof_of_partition_safety_wit_3 : partition_safety_wit_3.
Axiom proof_of_partition_safety_wit_4 : partition_safety_wit_4.
Axiom proof_of_partition_safety_wit_5 : partition_safety_wit_5.
Axiom proof_of_partition_safety_wit_6 : partition_safety_wit_6.
Axiom proof_of_partition_safety_wit_7 : partition_safety_wit_7.
Axiom proof_of_partition_safety_wit_8 : partition_safety_wit_8.
Axiom proof_of_partition_safety_wit_9 : partition_safety_wit_9.
Axiom proof_of_partition_entail_wit_1 : partition_entail_wit_1.
Axiom proof_of_partition_entail_wit_2 : partition_entail_wit_2.
Axiom proof_of_partition_entail_wit_3 : partition_entail_wit_3.
Axiom proof_of_partition_entail_wit_4 : partition_entail_wit_4.
Axiom proof_of_partition_entail_wit_5 : partition_entail_wit_5.
Axiom proof_of_partition_entail_wit_6 : partition_entail_wit_6.
Axiom proof_of_partition_return_wit_1 : partition_return_wit_1.
Axiom proof_of_partition_return_wit_2 : partition_return_wit_2.
Axiom proof_of_partition_partial_solve_wit_1 : partition_partial_solve_wit_1.
Axiom proof_of_partition_partial_solve_wit_2 : partition_partial_solve_wit_2.
Axiom proof_of_partition_partial_solve_wit_3 : partition_partial_solve_wit_3.
Axiom proof_of_partition_partial_solve_wit_4 : partition_partial_solve_wit_4.
Axiom proof_of_partition_partial_solve_wit_5 : partition_partial_solve_wit_5.
Axiom proof_of_partition_partial_solve_wit_6 : partition_partial_solve_wit_6.
Axiom proof_of_partition_partial_solve_wit_7 : partition_partial_solve_wit_7.
Axiom proof_of_partition_partial_solve_wit_8 : partition_partial_solve_wit_8.
Axiom proof_of_partition_partial_solve_wit_9 : partition_partial_solve_wit_9.
Axiom proof_of_quicksort_range_safety_wit_1 : quicksort_range_safety_wit_1.
Axiom proof_of_quicksort_range_safety_wit_2 : quicksort_range_safety_wit_2.
Axiom proof_of_quicksort_range_safety_wit_3 : quicksort_range_safety_wit_3.
Axiom proof_of_quicksort_range_safety_wit_4 : quicksort_range_safety_wit_4.
Axiom proof_of_quicksort_range_safety_wit_5 : quicksort_range_safety_wit_5.
Axiom proof_of_quicksort_range_safety_wit_6 : quicksort_range_safety_wit_6.
Axiom proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1.
Axiom proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2.
Axiom proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3.
Axiom proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4.
Axiom proof_of_quicksort_range_partial_solve_wit_1_pure : quicksort_range_partial_solve_wit_1_pure.
Axiom proof_of_quicksort_range_partial_solve_wit_1 : quicksort_range_partial_solve_wit_1.
Axiom proof_of_quicksort_range_partial_solve_wit_2_pure : quicksort_range_partial_solve_wit_2_pure.
Axiom proof_of_quicksort_range_partial_solve_wit_2 : quicksort_range_partial_solve_wit_2.
Axiom proof_of_quicksort_range_partial_solve_wit_3_pure : quicksort_range_partial_solve_wit_3_pure.
Axiom proof_of_quicksort_range_partial_solve_wit_3 : quicksort_range_partial_solve_wit_3.
Axiom proof_of_quicksort_range_partial_solve_wit_4_pure : quicksort_range_partial_solve_wit_4_pure.
Axiom proof_of_quicksort_range_partial_solve_wit_4 : quicksort_range_partial_solve_wit_4.
Axiom proof_of_quicksort_safety_wit_1 : quicksort_safety_wit_1.
Axiom proof_of_quicksort_safety_wit_2 : quicksort_safety_wit_2.
Axiom proof_of_quicksort_safety_wit_3 : quicksort_safety_wit_3.
Axiom proof_of_quicksort_safety_wit_4 : quicksort_safety_wit_4.
Axiom proof_of_quicksort_return_wit_1 : quicksort_return_wit_1.
Axiom proof_of_quicksort_return_wit_2 : quicksort_return_wit_2.
Axiom proof_of_quicksort_partial_solve_wit_1_pure : quicksort_partial_solve_wit_1_pure.
Axiom proof_of_quicksort_partial_solve_wit_1 : quicksort_partial_solve_wit_1.

End VC_Correct.
