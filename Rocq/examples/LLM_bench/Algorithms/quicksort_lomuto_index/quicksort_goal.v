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

(*----- Function swap -----*)

Definition swap_return_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) ,
  (IntArray.full arr_pre n (replace_Znth (j_pre) ((Znth i_pre l 0)) ((replace_Znth (i_pre) ((Znth j_pre l 0)) (l)))) )
|--
  (IntArray.full arr_pre n (replace_Znth (j_pre) ((Znth (i_pre) (l) (0))) ((replace_Znth (i_pre) ((Znth (j_pre) (l) (0))) (l)))) )
.

Definition swap_partial_solve_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) ,
  (IntArray.full arr_pre n l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ”
  &&  (((arr_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre l 0))
  **  (IntArray.missing_i arr_pre i_pre 0 n l )
.

Definition swap_partial_solve_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) ,
  (IntArray.full arr_pre n l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ”
  &&  (((arr_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre l 0))
  **  (IntArray.missing_i arr_pre j_pre 0 n l )
.

Definition swap_partial_solve_wit_3 := 
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) ,
  (IntArray.full arr_pre n l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ”
  &&  (((arr_pre + (i_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre i_pre 0 n l )
.

Definition swap_partial_solve_wit_4 := 
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n)) ,
  (IntArray.full arr_pre n (replace_Znth (i_pre) ((Znth j_pre l 0)) (l)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n) ”
  &&  (((arr_pre + (j_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre j_pre 0 n (replace_Znth (i_pre) ((Znth j_pre l 0)) (l)) )
.

(*----- Function partition -----*)

Definition partition_safety_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "pivot" ) )) # Int  |-> (Znth high_pre l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
|--
  “ ((low_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low_pre - 1 )) ”
.

Definition partition_safety_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "pivot" ) )) # Int  |-> (Znth high_pre l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_safety_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1 )) (PreH11 : (same_outside_range l l1 low_pre high_pre )) (PreH12 : ((Znth high_pre l1 0) = pivot)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_safety_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1 )) (PreH11 : (same_outside_range l l1 low_pre high_pre )) (PreH12 : ((Znth high_pre l1 0) = pivot)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth ((i + 1 )) (l1) (0))) ((replace_Znth ((i + 1 )) ((Znth (j) (l1) (0))) (l1)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_safety_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1 )) (PreH11 : (same_outside_range l l1 low_pre high_pre )) (PreH12 : ((Znth high_pre l1 0) = pivot)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition partition_safety_wit_6 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l 0))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1 )) (PreH10 : (same_outside_range l l1 low_pre high_pre )) (PreH11 : ((Znth high_pre l1 0) = pivot)) (PreH12 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH13 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l1 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_safety_wit_7 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l 0))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1 )) (PreH10 : (same_outside_range l l1 low_pre high_pre )) (PreH11 : ((Znth high_pre l1 0) = pivot)) (PreH12 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH13 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l1 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_safety_wit_8 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l 0))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1 )) (PreH10 : (same_outside_range l l1 low_pre high_pre )) (PreH11 : ((Znth high_pre l1 0) = pivot)) (PreH12 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH13 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n_pre (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1) (0))) (l1)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition partition_safety_wit_9 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l 0))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1 )) (PreH10 : (same_outside_range l l1 low_pre high_pre )) (PreH11 : ((Znth high_pre l1 0) = pivot)) (PreH12 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH13 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n_pre (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1) (0))) (l1)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition partition_entail_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  ((( &( "j" ) )) # Int  |-> low_pre)
  **  ((( &( "i" ) )) # Int  |-> (low_pre - 1 ))
  **  (IntArray.full arr_pre n_pre l )
  **  ((( &( "pivot" ) )) # Int  |-> (Znth high_pre l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
|--
  EX (l1: (@list Z))  (j: Z)  (i: Z)  (pivot: Z) ,
  “ (pivot = (Znth high_pre l 0)) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ ((Znth high_pre l1 0) = pivot) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  TT && emp 
|--
  “ forall (k_2: Z) , ((((low_pre - 1 ) < k_2) /\ (k_2 < low_pre)) -> ((Znth high_pre l 0) < (Znth k_2 l 0))) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k <= (low_pre - 1 ))) -> ((Znth k l 0) <= (Znth high_pre l 0))) ” 
  &&  “ (same_outside_range l l low_pre high_pre ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition partition_entail_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  forall (k_2: Z) , ((((low_pre - 1 ) < k_2) /\ (k_2 < low_pre)) -> ((Znth high_pre l 0) < (Znth k_2 l 0)))
.

Definition partition_entail_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  forall (k: Z) , (((low_pre <= k) /\ (k <= (low_pre - 1 ))) -> ((Znth k l 0) <= (Znth high_pre l 0)))
.

Definition partition_entail_wit_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  (same_outside_range l l low_pre high_pre )
.

Definition partition_entail_wit_1_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) ,
  (Permutation l l )
.

Definition partition_entail_wit_2_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH2 : (j_2 < high_pre)) (PreH3 : (pivot_2 = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i_2)) (PreH8 : (i_2 < j_2)) (PreH9 : (j_2 <= high_pre)) (PreH10 : (Permutation l l1_2 )) (PreH11 : (same_outside_range l l1_2 low_pre high_pre )) (PreH12 : ((Znth high_pre l1_2 0) = pivot_2)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i_2)) -> ((Znth k l1_2 0) <= pivot_2))) (PreH14 : forall (k_2: Z) , (((i_2 < k_2) /\ (k_2 < j_2)) -> (pivot_2 < (Znth k_2 l1_2 0)))) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_2)
  **  ((( &( "i" ) )) # Int  |-> (i_2 + 1 ))
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
|--
  EX (l1: (@list Z))  (j: Z)  (i: Z)  (pivot: Z) ,
  “ (pivot = (Znth high_pre l 0)) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ ((Znth high_pre l1 0) = pivot) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l 0))) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 low_pre high_pre )) (PreH13 : ((Znth high_pre l1_2 0) = pivot_2)) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k <= i_2)) -> ((Znth k l1_2 0) <= pivot_2))) (PreH15 : forall (k_2: Z) , (((i_2 < k_2) /\ (k_2 < j_2)) -> (pivot_2 < (Znth k_2 l1_2 0)))) ,
  TT && emp 
|--
  “ ((Znth high_pre (replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))) 0) = pivot_2) ” 
  &&  “ (same_outside_range l (replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))) low_pre high_pre ) ” 
  &&  “ (Permutation l (replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))) ) ”
  &&  emp
).

Definition partition_entail_wit_2_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l 0))) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 low_pre high_pre )) (PreH13 : ((Znth high_pre l1_2 0) = pivot_2)) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k <= i_2)) -> ((Znth k l1_2 0) <= pivot_2))) (PreH15 : forall (k_2: Z) , (((i_2 < k_2) /\ (k_2 < j_2)) -> (pivot_2 < (Znth k_2 l1_2 0)))) ,
  ((Znth high_pre (replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))) 0) = pivot_2)
.

Definition partition_entail_wit_2_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l 0))) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 low_pre high_pre )) (PreH13 : ((Znth high_pre l1_2 0) = pivot_2)) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k <= i_2)) -> ((Znth k l1_2 0) <= pivot_2))) (PreH15 : forall (k_2: Z) , (((i_2 < k_2) /\ (k_2 < j_2)) -> (pivot_2 < (Znth k_2 l1_2 0)))) ,
  (same_outside_range l (replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))) low_pre high_pre )
.

Definition partition_entail_wit_2_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Zlength ((replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))))) = n_pre)) (PreH2 : ((Znth j_2 l1_2 0) <= pivot_2)) (PreH3 : (j_2 < high_pre)) (PreH4 : (pivot_2 = (Znth high_pre l 0))) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= high_pre)) (PreH7 : (high_pre < n_pre)) (PreH8 : ((low_pre - 1 ) <= i_2)) (PreH9 : (i_2 < j_2)) (PreH10 : (j_2 <= high_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 low_pre high_pre )) (PreH13 : ((Znth high_pre l1_2 0) = pivot_2)) (PreH14 : forall (k: Z) , (((low_pre <= k) /\ (k <= i_2)) -> ((Znth k l1_2 0) <= pivot_2))) (PreH15 : forall (k_2: Z) , (((i_2 < k_2) /\ (k_2 < j_2)) -> (pivot_2 < (Znth k_2 l1_2 0)))) ,
  (Permutation l (replace_Znth (j_2) ((Znth ((i_2 + 1 )) (l1_2) (0))) ((replace_Znth ((i_2 + 1 )) ((Znth (j_2) (l1_2) (0))) (l1_2)))) )
.

Definition partition_entail_wit_2_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j_2: Z) (i_2: Z) (pivot_2: Z) (PreH1 : ((Znth j_2 l1_2 0) > pivot_2)) (PreH2 : (j_2 < high_pre)) (PreH3 : (pivot_2 = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i_2)) (PreH8 : (i_2 < j_2)) (PreH9 : (j_2 <= high_pre)) (PreH10 : (Permutation l l1_2 )) (PreH11 : (same_outside_range l l1_2 low_pre high_pre )) (PreH12 : ((Znth high_pre l1_2 0) = pivot_2)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i_2)) -> ((Znth k l1_2 0) <= pivot_2))) (PreH14 : forall (k_2: Z) , (((i_2 < k_2) /\ (k_2 < j_2)) -> (pivot_2 < (Znth k_2 l1_2 0)))) ,
  (IntArray.full arr_pre n_pre l1_2 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot_2)
  **  ((( &( "i" ) )) # Int  |-> i_2)
  **  ((( &( "j" ) )) # Int  |-> (j_2 + 1 ))
|--
  EX (l1: (@list Z))  (j: Z)  (i: Z)  (pivot: Z) ,
  “ (pivot = (Znth high_pre l 0)) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ ((Znth high_pre l1 0) = pivot) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0))) ”
  &&  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre l1 )
.

Definition partition_return_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l 0))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 low_pre high_pre )) (PreH11 : ((Znth high_pre l1_2 0) = pivot)) (PreH12 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1_2 0) <= pivot))) (PreH13 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1_2 0)))) ,
  (IntArray.full arr_pre n_pre (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))) )
|--
  EX (l1: (@list Z)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ (partitioned_at l1 low_pre high_pre (i + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))))) = n_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (pivot = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1_2 )) (PreH11 : (same_outside_range l l1_2 low_pre high_pre )) (PreH12 : ((Znth high_pre l1_2 0) = pivot)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1_2 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1_2 0)))) ,
  TT && emp 
|--
  “ (partitioned_at (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) (pivot) (l1_2)))) low_pre high_pre (i + 1 ) ) ” 
  &&  “ (same_outside_range l (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) (pivot) (l1_2)))) low_pre high_pre ) ” 
  &&  “ (Permutation l (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) (pivot) (l1_2)))) ) ”
  &&  emp
).

Definition partition_return_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))))) = n_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (pivot = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1_2 )) (PreH11 : (same_outside_range l l1_2 low_pre high_pre )) (PreH12 : ((Znth high_pre l1_2 0) = pivot)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1_2 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1_2 0)))) ,
  (partitioned_at (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) (pivot) (l1_2)))) low_pre high_pre (i + 1 ) )
.

Definition partition_return_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))))) = n_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (pivot = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1_2 )) (PreH11 : (same_outside_range l l1_2 low_pre high_pre )) (PreH12 : ((Znth high_pre l1_2 0) = pivot)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1_2 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1_2 0)))) ,
  (same_outside_range l (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) (pivot) (l1_2)))) low_pre high_pre )
.

Definition partition_return_wit_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Zlength ((replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))))) = n_pre)) (PreH2 : (j >= high_pre)) (PreH3 : (pivot = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1_2 )) (PreH11 : (same_outside_range l l1_2 low_pre high_pre )) (PreH12 : ((Znth high_pre l1_2 0) = pivot)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1_2 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1_2 0)))) ,
  (Permutation l (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) (pivot) (l1_2)))) )
.

Definition partition_partial_solve_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ”
  &&  (((arr_pre + (high_pre * sizeof(INT)))) # Int  |-> (Znth high_pre l 0))
  **  (IntArray.missing_i arr_pre high_pre 0 n_pre l )
.

Definition partition_partial_solve_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j < high_pre)) (PreH2 : (pivot = (Znth high_pre l 0))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1 )) (PreH10 : (same_outside_range l l1 low_pre high_pre )) (PreH11 : ((Znth high_pre l1 0) = pivot)) (PreH12 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH13 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (j < high_pre) ” 
  &&  “ (pivot = (Znth high_pre l 0)) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ ((Znth high_pre l1 0) = pivot) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0))) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l1 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre l1 )
.

Definition partition_partial_solve_wit_3_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1 )) (PreH11 : (same_outside_range l l1 low_pre high_pre )) (PreH12 : ((Znth high_pre l1 0) = pivot)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ”
.

Definition partition_partial_solve_wit_3_aux := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth high_pre l 0))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (Permutation l l1 )) (PreH11 : (same_outside_range l l1 low_pre high_pre )) (PreH12 : ((Znth high_pre l1 0) = pivot)) (PreH13 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH14 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((Znth j l1 0) <= pivot) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (pivot = (Znth high_pre l 0)) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ ((Znth high_pre l1 0) = pivot) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0))) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition partition_partial_solve_wit_3 := partition_partial_solve_wit_3_pure -> partition_partial_solve_wit_3_aux.

Definition partition_partial_solve_wit_4_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l 0))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1 )) (PreH10 : (same_outside_range l l1 low_pre high_pre )) (PreH11 : ((Znth high_pre l1 0) = pivot)) (PreH12 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH13 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ”
.

Definition partition_partial_solve_wit_4_aux := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth high_pre l 0))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (Permutation l l1 )) (PreH10 : (same_outside_range l l1 low_pre high_pre )) (PreH11 : ((Znth high_pre l1 0) = pivot)) (PreH12 : forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot))) (PreH13 : forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0)))) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ (pivot = (Znth high_pre l 0)) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ ((Znth high_pre l1 0) = pivot) ” 
  &&  “ forall (k: Z) , (((low_pre <= k) /\ (k <= i)) -> ((Znth k l1 0) <= pivot)) ” 
  &&  “ forall (k_2: Z) , (((i < k_2) /\ (k_2 < j)) -> (pivot < (Znth k_2 l1 0))) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition partition_partial_solve_wit_4 := partition_partial_solve_wit_4_pure -> partition_partial_solve_wit_4_aux.

(*----- Function quicksort_range -----*)

Definition quicksort_range_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quicksort_range_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_range_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ False ”
.

Definition quicksort_range_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_range_safety_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_range_safety_wit_6 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_range_safety_wit_7 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_range_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (Permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (Permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (0 <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_4 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : ((Zlength (l1_4)) = n_pre)) (PreH2 : (Permutation l1_3 l1_4 )) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3 )) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2 )) (PreH13 : (same_outside_range l l1_2 left_pre right_pre )) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (0 <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_4 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_4 left_pre right_pre ) ” 
  &&  “ (Permutation l l1_4 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : ((Zlength (l1_4)) = n_pre)) (PreH2 : (Permutation l1_3 l1_4 )) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3 )) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2 )) (PreH13 : (same_outside_range l l1_2 left_pre right_pre )) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (0 <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) ,
  (range_nondecreasing l1_4 left_pre right_pre )
.

Definition quicksort_range_return_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : ((Zlength (l1_4)) = n_pre)) (PreH2 : (Permutation l1_3 l1_4 )) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3 )) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2 )) (PreH13 : (same_outside_range l l1_2 left_pre right_pre )) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (0 <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) ,
  (same_outside_range l l1_4 left_pre right_pre )
.

Definition quicksort_range_return_wit_1_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : ((Zlength (l1_4)) = n_pre)) (PreH2 : (Permutation l1_3 l1_4 )) (PreH3 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (Permutation l1_2 l1_3 )) (PreH7 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH8 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1_2 )) (PreH13 : (same_outside_range l l1_2 left_pre right_pre )) (PreH14 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (0 <= left_pre)) (PreH18 : ((-1) <= right_pre)) (PreH19 : (right_pre < n_pre)) ,
  (Permutation l l1_4 )
.

Definition quicksort_range_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (Permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_3 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_3 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_3 left_pre right_pre ) ” 
  &&  “ (Permutation l l1_3 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (range_nondecreasing l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_2_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_2_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH4 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH5 : (retval < right_pre)) (PreH6 : (retval <= left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (Permutation l l1_3 )
.

Definition quicksort_range_return_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_3 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3 )) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_3 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_3 left_pre right_pre ) ” 
  &&  “ (Permutation l l1_3 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3 )) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (range_nondecreasing l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_3_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3 )) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_3_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : ((Zlength (l1_3)) = n_pre)) (PreH2 : (retval >= right_pre)) (PreH3 : (Permutation l1_2 l1_3 )) (PreH4 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH5 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (Permutation l l1_2 )) (PreH10 : (same_outside_range l l1_2 left_pre right_pre )) (PreH11 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH12 : (left_pre < right_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (0 <= left_pre)) (PreH15 : ((-1) <= right_pre)) (PreH16 : (right_pre < n_pre)) ,
  (Permutation l l1_3 )
.

Definition quicksort_range_return_wit_4 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (left_pre >= right_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l left_pre right_pre ) ” 
  &&  “ (same_outside_range l l left_pre right_pre ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition quicksort_range_return_wit_4_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (left_pre >= right_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) ,
  (range_nondecreasing l left_pre right_pre )
.

Definition quicksort_range_return_wit_4_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (left_pre >= right_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) ,
  (same_outside_range l l left_pre right_pre )
.

Definition quicksort_range_return_wit_4_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (left_pre >= right_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) ,
  (Permutation l l )
.

Definition quicksort_range_partial_solve_wit_1_pure := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ”
.

Definition quicksort_range_partial_solve_wit_1_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (left_pre < right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition quicksort_range_partial_solve_wit_1 := quicksort_range_partial_solve_wit_1_pure -> quicksort_range_partial_solve_wit_1_aux.

Definition quicksort_range_partial_solve_wit_2_pure := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ”
.

Definition quicksort_range_partial_solve_wit_2_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (partitioned_at l1 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition quicksort_range_partial_solve_wit_2 := quicksort_range_partial_solve_wit_2_pure -> quicksort_range_partial_solve_wit_2_aux.

Definition quicksort_range_partial_solve_wit_3_pure := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ”
.

Definition quicksort_range_partial_solve_wit_3_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
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
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1_2 )
.

Definition quicksort_range_partial_solve_wit_3 := quicksort_range_partial_solve_wit_3_pure -> quicksort_range_partial_solve_wit_3_aux.

Definition quicksort_range_partial_solve_wit_4_pure := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ”
.

Definition quicksort_range_partial_solve_wit_4_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (partitioned_at l1 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition quicksort_range_partial_solve_wit_4 := quicksort_range_partial_solve_wit_4_pure -> quicksort_range_partial_solve_wit_4_aux.

(*----- Function quicksort -----*)

Definition quicksort_safety_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition quicksort_safety_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_safety_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_return_wit_1 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : (Permutation l l1_2 )) (PreH2 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH3 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : ((Zlength (l1_2)) = n_pre)) (PreH2 : (Permutation l l1_2 )) (PreH3 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH4 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ (increasing l1_2 ) ”
  &&  emp
).

Definition quicksort_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : ((Zlength (l1_2)) = n_pre)) (PreH2 : (Permutation l l1_2 )) (PreH3 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH4 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) ,
  (increasing l1_2 )
.

Definition quicksort_partial_solve_wit_1_pure := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ”
.

Definition quicksort_partial_solve_wit_1_aux := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (n_pre - 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition quicksort_partial_solve_wit_1 := quicksort_partial_solve_wit_1_pure -> quicksort_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_swap_return_wit_1 : swap_return_wit_1.
Axiom proof_of_swap_partial_solve_wit_1 : swap_partial_solve_wit_1.
Axiom proof_of_swap_partial_solve_wit_2 : swap_partial_solve_wit_2.
Axiom proof_of_swap_partial_solve_wit_3 : swap_partial_solve_wit_3.
Axiom proof_of_swap_partial_solve_wit_4 : swap_partial_solve_wit_4.
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
Axiom proof_of_partition_entail_wit_2_1 : partition_entail_wit_2_1.
Axiom proof_of_partition_entail_wit_2_2 : partition_entail_wit_2_2.
Axiom proof_of_partition_return_wit_1 : partition_return_wit_1.
Axiom proof_of_partition_partial_solve_wit_1 : partition_partial_solve_wit_1.
Axiom proof_of_partition_partial_solve_wit_2 : partition_partial_solve_wit_2.
Axiom proof_of_partition_partial_solve_wit_3_pure : partition_partial_solve_wit_3_pure.
Axiom proof_of_partition_partial_solve_wit_3 : partition_partial_solve_wit_3.
Axiom proof_of_partition_partial_solve_wit_4_pure : partition_partial_solve_wit_4_pure.
Axiom proof_of_partition_partial_solve_wit_4 : partition_partial_solve_wit_4.
Axiom proof_of_quicksort_range_safety_wit_1 : quicksort_range_safety_wit_1.
Axiom proof_of_quicksort_range_safety_wit_2 : quicksort_range_safety_wit_2.
Axiom proof_of_quicksort_range_safety_wit_3 : quicksort_range_safety_wit_3.
Axiom proof_of_quicksort_range_safety_wit_4 : quicksort_range_safety_wit_4.
Axiom proof_of_quicksort_range_safety_wit_5 : quicksort_range_safety_wit_5.
Axiom proof_of_quicksort_range_safety_wit_6 : quicksort_range_safety_wit_6.
Axiom proof_of_quicksort_range_safety_wit_7 : quicksort_range_safety_wit_7.
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
Axiom proof_of_quicksort_return_wit_1 : quicksort_return_wit_1.
Axiom proof_of_quicksort_partial_solve_wit_1_pure : quicksort_partial_solve_wit_1_pure.
Axiom proof_of_quicksort_partial_solve_wit_1 : quicksort_partial_solve_wit_1.

End VC_Correct.
