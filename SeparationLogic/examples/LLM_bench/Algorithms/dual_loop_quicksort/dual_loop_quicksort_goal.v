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
Require Import SimpleC.EE.LLM_bench.Algorithms.dual_loop_quicksort.dual_loop_quicksort_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function swap -----*)

Definition swap_return_wit_1 := 
(
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n0: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n0)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n0)) ,
  (IntArray.full arr_pre n0 (replace_Znth (j_pre) ((Znth i_pre l 0)) ((replace_Znth (i_pre) ((Znth j_pre l 0)) (l)))) )
|--
  (IntArray.full arr_pre n0 (replace_Znth (j_pre) ((Znth (i_pre) (l) (0))) ((replace_Znth (i_pre) ((Znth (j_pre) (l) (0))) (l)))) )
) \/
(
forall (j_pre: Z) (i_pre: Z) (l: (@list Z)) (n0: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n0)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n0)) ,
  TT && emp 
|--
  “ ((replace_Znth (j_pre) ((Znth i_pre l 0)) ((replace_Znth (i_pre) ((Znth j_pre l 0)) (l)))) = (replace_Znth (j_pre) ((Znth (i_pre) (l) (0))) ((replace_Znth (i_pre) ((Znth (j_pre) (l) (0))) (l))))) ”
  &&  emp
).

Definition swap_return_wit_1_split_goal_1 := 
forall (j_pre: Z) (i_pre: Z) (l: (@list Z)) (n0: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n0)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n0)) ,
  ((replace_Znth (j_pre) ((Znth i_pre l 0)) ((replace_Znth (i_pre) ((Znth j_pre l 0)) (l)))) = (replace_Znth (j_pre) ((Znth (i_pre) (l) (0))) ((replace_Znth (i_pre) ((Znth (j_pre) (l) (0))) (l)))))
.

Definition swap_partial_solve_wit_1 := 
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n0: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n0)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n0)) ,
  (IntArray.full arr_pre n0 l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n0) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n0) ”
  &&  (((arr_pre + (i_pre * sizeof(INT)))) # Int  |-> (Znth i_pre l 0))
  **  (IntArray.missing_i arr_pre i_pre 0 n0 l )
.

Definition swap_partial_solve_wit_2 := 
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n0: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n0)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n0)) ,
  (IntArray.full arr_pre n0 l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n0) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n0) ”
  &&  (((arr_pre + (j_pre * sizeof(INT)))) # Int  |-> (Znth j_pre l 0))
  **  (IntArray.missing_i arr_pre j_pre 0 n0 l )
.

Definition swap_partial_solve_wit_3 := 
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n0: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n0)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n0)) ,
  (IntArray.full arr_pre n0 l )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n0) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n0) ”
  &&  (((arr_pre + (i_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre i_pre 0 n0 l )
.

Definition swap_partial_solve_wit_4 := 
forall (j_pre: Z) (i_pre: Z) (arr_pre: Z) (l: (@list Z)) (n0: Z) (PreH1 : (0 <= i_pre)) (PreH2 : (i_pre < n0)) (PreH3 : (0 <= j_pre)) (PreH4 : (j_pre < n0)) ,
  (IntArray.full arr_pre n0 (replace_Znth (i_pre) ((Znth j_pre l 0)) (l)) )
|--
  “ (0 <= i_pre) ” 
  &&  “ (i_pre < n0) ” 
  &&  “ (0 <= j_pre) ” 
  &&  “ (j_pre < n0) ”
  &&  (((arr_pre + (j_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i arr_pre j_pre 0 n0 (replace_Znth (i_pre) ((Znth j_pre l 0)) (l)) )
.

(*----- Function partition_two_loop -----*)

Definition partition_two_loop_safety_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) >= pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_right_scan_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition partition_two_loop_safety_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth i l1 0) <= pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_left_scan_inv l l1 low_pre high_pre pivot i j )) ,
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

Definition partition_two_loop_safety_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_left_scan_inv l l1 low_pre high_pre pivot i j )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre l1 )
|--
  “ False ”
.

Definition partition_two_loop_safety_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : ((Znth i l1 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth (low_pre) (l) (0)))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : (low_pre <= i)) (PreH12 : (i <= j)) (PreH13 : (j <= high_pre)) (PreH14 : (partition_left_scan_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ False ”
.

Definition partition_two_loop_entail_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ ((Znth low_pre l 0) = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre <= high_pre) ” 
  &&  “ (partition_outer_inv l l1 low_pre high_pre (Znth low_pre l 0) low_pre high_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) ,
  TT && emp 
|--
  “ (partition_outer_inv l l low_pre high_pre (Znth low_pre l 0) low_pre high_pre ) ” 
  &&  “ ((Znth low_pre l 0) = (Znth (low_pre) (l) (0))) ”
  &&  emp
).

Definition partition_two_loop_entail_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) ,
  (partition_outer_inv l l low_pre high_pre (Znth low_pre l 0) low_pre high_pre )
.

Definition partition_two_loop_entail_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) ,
  ((Znth low_pre l 0) = (Znth (low_pre) (l) (0)))
.

Definition partition_two_loop_entail_wit_2 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_right_scan_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j ) ”
  &&  emp
).

Definition partition_two_loop_entail_wit_2_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )
.

Definition partition_two_loop_entail_wit_3 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) >= pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= (j - 1 )) ” 
  &&  “ ((j - 1 ) <= high_pre) ” 
  &&  “ (partition_right_scan_inv l l1 low_pre high_pre pivot i (j - 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) >= pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partition_right_scan_inv l l1_2 low_pre high_pre pivot i (j - 1 ) ) ”
  &&  emp
).

Definition partition_two_loop_entail_wit_3_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) >= pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partition_right_scan_inv l l1_2 low_pre high_pre pivot i (j - 1 ) )
.

Definition partition_two_loop_entail_wit_4_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_left_scan_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j ) ”
  &&  emp
).

Definition partition_two_loop_entail_wit_4_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )
.

Definition partition_two_loop_entail_wit_4_2 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) < pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_left_scan_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) < pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j ) ”
  &&  emp
).

Definition partition_two_loop_entail_wit_4_2_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) < pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_right_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )
.

Definition partition_two_loop_entail_wit_5 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth i l1_2 0) <= pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_left_scan_inv l l1 low_pre high_pre pivot (i + 1 ) j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth i l1_2 0) <= pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partition_left_scan_inv l l1_2 low_pre high_pre pivot (i + 1 ) j ) ”
  &&  emp
).

Definition partition_two_loop_entail_wit_5_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth i l1_2 0) <= pivot)) (PreH2 : (i < j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partition_left_scan_inv l l1_2 low_pre high_pre pivot (i + 1 ) j )
.

Definition partition_two_loop_entail_wit_6_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth i l1_2 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth (low_pre) (l) (0)))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : (low_pre <= i)) (PreH12 : (i <= j)) (PreH13 : (j <= high_pre)) (PreH14 : (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth (i) (l1_2) (0))) ((replace_Znth (i) ((Znth (j) (l1_2) (0))) (l1_2)))) )
|--
  EX (l1: (@list Z)) ,
  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_outer_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth i l1_2 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth (low_pre) (l) (0)))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : (low_pre <= i)) (PreH12 : (i <= j)) (PreH13 : (j <= high_pre)) (PreH14 : (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partition_outer_inv l (replace_Znth (j) ((Znth (i) (l1_2) (0))) ((replace_Znth (i) ((Znth (j) (l1_2) (0))) (l1_2)))) low_pre high_pre pivot i j ) ”
  &&  emp
).

Definition partition_two_loop_entail_wit_6_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth i l1_2 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth (low_pre) (l) (0)))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : (low_pre <= i)) (PreH12 : (i <= j)) (PreH13 : (j <= high_pre)) (PreH14 : (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partition_outer_inv l (replace_Znth (j) ((Znth (i) (l1_2) (0))) ((replace_Znth (i) ((Znth (j) (l1_2) (0))) (l1_2)))) low_pre high_pre pivot i j )
.

Definition partition_two_loop_entail_wit_6_2 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_outer_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partition_outer_inv l l1_2 low_pre high_pre pivot i j ) ”
  &&  emp
).

Definition partition_two_loop_entail_wit_6_2_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (i >= j)) (PreH3 : (pivot = (Znth (low_pre) (l) (0)))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= high_pre)) (PreH9 : (high_pre < n_pre)) (PreH10 : (low_pre <= i)) (PreH11 : (i <= j)) (PreH12 : (j <= high_pre)) (PreH13 : (partition_left_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partition_outer_inv l l1_2 low_pre high_pre pivot i j )
.

Definition partition_two_loop_return_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre (replace_Znth (i) ((Znth (low_pre) (l1_2) (0))) ((replace_Znth (low_pre) ((Znth (i) (l1_2) (0))) (l1_2)))) )
|--
  EX (l1: (@list Z)) ,
  “ (low_pre <= i) ” 
  &&  “ (i <= high_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ (partitioned_at l1 low_pre high_pre i ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partitioned_at (replace_Znth (i) ((Znth (low_pre) (l1_2) (0))) ((replace_Znth (low_pre) ((Znth (i) (l1_2) (0))) (l1_2)))) low_pre high_pre i ) ” 
  &&  “ (same_outside_range l (replace_Znth (i) ((Znth (low_pre) (l1_2) (0))) ((replace_Znth (low_pre) ((Znth (i) (l1_2) (0))) (l1_2)))) low_pre high_pre ) ” 
  &&  “ (Permutation l (replace_Znth (i) ((Znth (low_pre) (l1_2) (0))) ((replace_Znth (low_pre) ((Znth (i) (l1_2) (0))) (l1_2)))) ) ”
  &&  emp
).

Definition partition_two_loop_return_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partitioned_at (replace_Znth (i) ((Znth (low_pre) (l1_2) (0))) ((replace_Znth (low_pre) ((Znth (i) (l1_2) (0))) (l1_2)))) low_pre high_pre i )
.

Definition partition_two_loop_return_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1_2 low_pre high_pre pivot i j )) ,
  (same_outside_range l (replace_Znth (i) ((Znth (low_pre) (l1_2) (0))) ((replace_Znth (low_pre) ((Znth (i) (l1_2) (0))) (l1_2)))) low_pre high_pre )
.

Definition partition_two_loop_return_wit_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1_2 low_pre high_pre pivot i j )) ,
  (Permutation l (replace_Znth (i) ((Znth (low_pre) (l1_2) (0))) ((replace_Znth (low_pre) ((Znth (i) (l1_2) (0))) (l1_2)))) )
.

Definition partition_two_loop_partial_solve_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ”
  &&  (((arr_pre + (low_pre * sizeof(INT)))) # Int  |-> (Znth low_pre l 0))
  **  (IntArray.missing_i arr_pre low_pre 0 n_pre l )
.

Definition partition_two_loop_partial_solve_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_right_scan_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (i < j) ” 
  &&  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_right_scan_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l1 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre l1 )
.

Definition partition_two_loop_partial_solve_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_left_scan_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (i < j) ” 
  &&  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_left_scan_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l1 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l1 )
.

Definition partition_two_loop_partial_solve_wit_4_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth i l1 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth (low_pre) (l) (0)))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : (low_pre <= i)) (PreH12 : (i <= j)) (PreH13 : (j <= high_pre)) (PreH14 : (partition_left_scan_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ”
.

Definition partition_two_loop_partial_solve_wit_4_aux := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i < j)) (PreH2 : ((Znth i l1 0) > pivot)) (PreH3 : (i < j)) (PreH4 : (pivot = (Znth (low_pre) (l) (0)))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (1 <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= high_pre)) (PreH10 : (high_pre < n_pre)) (PreH11 : (low_pre <= i)) (PreH12 : (i <= j)) (PreH13 : (j <= high_pre)) (PreH14 : (partition_left_scan_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ (i < j) ” 
  &&  “ ((Znth i l1 0) > pivot) ” 
  &&  “ (i < j) ” 
  &&  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_left_scan_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition partition_two_loop_partial_solve_wit_4 := partition_two_loop_partial_solve_wit_4_pure -> partition_two_loop_partial_solve_wit_4_aux.

Definition partition_two_loop_partial_solve_wit_5_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1 low_pre high_pre pivot i j )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ”
.

Definition partition_two_loop_partial_solve_wit_5_aux := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (i >= j)) (PreH2 : (pivot = (Znth (low_pre) (l) (0)))) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : (low_pre <= i)) (PreH10 : (i <= j)) (PreH11 : (j <= high_pre)) (PreH12 : (partition_outer_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= low_pre) ” 
  &&  “ (low_pre < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (i >= j) ” 
  &&  “ (pivot = (Znth (low_pre) (l) (0))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (low_pre <= i) ” 
  &&  “ (i <= j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_outer_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition partition_two_loop_partial_solve_wit_5 := partition_two_loop_partial_solve_wit_5_pure -> partition_two_loop_partial_solve_wit_5_aux.

(*----- Function quicksort_range -----*)

Definition quicksort_range_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : (left_pre <= (right_pre + 1 ))) (PreH13 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition quicksort_range_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : (left_pre <= (right_pre + 1 ))) (PreH13 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_range_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 50000)) (PreH12 : (0 <= left_pre)) (PreH13 : (left_pre <= (right_pre + 1 ))) (PreH14 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ False ”
.

Definition quicksort_range_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_range_safety_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_2 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_range_safety_wit_6 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 50000)) (PreH12 : (0 <= left_pre)) (PreH13 : (left_pre <= (right_pre + 1 ))) (PreH14 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition quicksort_range_safety_wit_7 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 50000)) (PreH12 : (0 <= left_pre)) (PreH13 : (left_pre <= (right_pre + 1 ))) (PreH14 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_range_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (Permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (Permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : ((Zlength (l)) = n_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : (left_pre <= (right_pre + 1 ))) (PreH20 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_4 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (Permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (Permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : ((Zlength (l)) = n_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : (left_pre <= (right_pre + 1 ))) (PreH20 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_4 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_4 left_pre right_pre ) ” 
  &&  “ (Permutation l l1_4 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (Permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (Permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : ((Zlength (l)) = n_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : (left_pre <= (right_pre + 1 ))) (PreH20 : (right_pre < n_pre)) ,
  (range_nondecreasing l1_4 left_pre right_pre )
.

Definition quicksort_range_return_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (Permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (Permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : ((Zlength (l)) = n_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : (left_pre <= (right_pre + 1 ))) (PreH20 : (right_pre < n_pre)) ,
  (same_outside_range l l1_4 left_pre right_pre )
.

Definition quicksort_range_return_wit_1_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (Permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (Permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (Permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : ((Zlength (l)) = n_pre)) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 50000)) (PreH18 : (0 <= left_pre)) (PreH19 : (left_pre <= (right_pre + 1 ))) (PreH20 : (right_pre < n_pre)) ,
  (Permutation l l1_4 )
.

Definition quicksort_range_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (Permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_3 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (Permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_3 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_3 left_pre right_pre ) ” 
  &&  “ (Permutation l l1_3 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (Permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (range_nondecreasing l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_2_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (Permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_2_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (Permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (range_nondecreasing l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (Permutation l l1_3 )
.

Definition quicksort_range_return_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_3 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l1_3 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_3 left_pre right_pre ) ” 
  &&  “ (Permutation l l1_3 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (range_nondecreasing l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_3_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_3_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (Permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (Permutation l l1_3 )
.

Definition quicksort_range_return_wit_4 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= (right_pre + 1 ))) (PreH7 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (range_nondecreasing l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= (right_pre + 1 ))) (PreH7 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (range_nondecreasing l left_pre right_pre ) ” 
  &&  “ (same_outside_range l l left_pre right_pre ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition quicksort_range_return_wit_4_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= (right_pre + 1 ))) (PreH7 : (right_pre < n_pre)) ,
  (range_nondecreasing l left_pre right_pre )
.

Definition quicksort_range_return_wit_4_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= (right_pre + 1 ))) (PreH7 : (right_pre < n_pre)) ,
  (same_outside_range l l left_pre right_pre )
.

Definition quicksort_range_return_wit_4_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= (right_pre + 1 ))) (PreH7 : (right_pre < n_pre)) ,
  (Permutation l l )
.

Definition quicksort_range_partial_solve_wit_1_pure := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (left_pre < right_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= (right_pre + 1 ))) (PreH7 : (right_pre < n_pre)) ,
  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ”
.

Definition quicksort_range_partial_solve_wit_1_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (left_pre < right_pre)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= (right_pre + 1 ))) (PreH7 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (right_pre + 1 )) ” 
  &&  “ (right_pre < n_pre) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition quicksort_range_partial_solve_wit_1 := quicksort_range_partial_solve_wit_1_pure -> quicksort_range_partial_solve_wit_1_aux.

Definition quicksort_range_partial_solve_wit_2_pure := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : (left_pre <= (right_pre + 1 ))) (PreH13 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= ((retval - 1 ) + 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1 )) (PreH13 : (same_outside_range l l1 left_pre right_pre )) (PreH14 : (partitioned_at l1 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 50000)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre <= (right_pre + 1 ))) (PreH21 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ ((Zlength (l1)) = n_pre) ”
).

Definition quicksort_range_partial_solve_wit_2_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval > left_pre)) (PreH10 : (left_pre <= retval)) (PreH11 : (retval <= right_pre)) (PreH12 : (Permutation l l1 )) (PreH13 : (same_outside_range l l1 left_pre right_pre )) (PreH14 : (partitioned_at l1 left_pre right_pre retval )) (PreH15 : (left_pre < right_pre)) (PreH16 : ((Zlength (l)) = n_pre)) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 50000)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre <= (right_pre + 1 ))) (PreH21 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ ((Zlength (l1)) = n_pre) ”
.

Definition quicksort_range_partial_solve_wit_2_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (Permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : (0 <= left_pre)) (PreH12 : (left_pre <= (right_pre + 1 ))) (PreH13 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= ((retval - 1 ) + 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ ((Zlength (l1)) = n_pre) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (partitioned_at l1 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (right_pre + 1 )) ” 
  &&  “ (right_pre < n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition quicksort_range_partial_solve_wit_2 := quicksort_range_partial_solve_wit_2_pure -> quicksort_range_partial_solve_wit_2_aux.

Definition quicksort_range_partial_solve_wit_3_pure := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1_2 l1 )) (PreH3 : (same_outside_range l1_2 l1 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= (right_pre + 1 )) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (Permutation l1_2 l1 )) (PreH11 : (same_outside_range l1_2 l1 left_pre (retval - 1 ) )) (PreH12 : (range_nondecreasing l1 left_pre (retval - 1 ) )) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (Permutation l l1_2 )) (PreH17 : (same_outside_range l l1_2 left_pre right_pre )) (PreH18 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : (0 <= left_pre)) (PreH24 : (left_pre <= (right_pre + 1 ))) (PreH25 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ ((Zlength (l1)) = n_pre) ”
).

Definition quicksort_range_partial_solve_wit_3_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1: (@list Z)) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (Permutation l1_2 l1 )) (PreH11 : (same_outside_range l1_2 l1 left_pre (retval - 1 ) )) (PreH12 : (range_nondecreasing l1 left_pre (retval - 1 ) )) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (Permutation l l1_2 )) (PreH17 : (same_outside_range l l1_2 left_pre right_pre )) (PreH18 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH19 : (left_pre < right_pre)) (PreH20 : ((Zlength (l)) = n_pre)) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : (0 <= left_pre)) (PreH24 : (left_pre <= (right_pre + 1 ))) (PreH25 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ ((Zlength (l1)) = n_pre) ”
.

Definition quicksort_range_partial_solve_wit_3_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (Permutation l1_2 l1 )) (PreH3 : (same_outside_range l1_2 l1 left_pre (retval - 1 ) )) (PreH4 : (range_nondecreasing l1 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (Permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : (0 <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : (0 <= left_pre)) (PreH16 : (left_pre <= (right_pre + 1 ))) (PreH17 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= (right_pre + 1 )) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (l1)) = n_pre) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (Permutation l1_2 l1 ) ” 
  &&  “ (same_outside_range l1_2 l1 left_pre (retval - 1 ) ) ” 
  &&  “ (range_nondecreasing l1 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (Permutation l l1_2 ) ” 
  &&  “ (same_outside_range l l1_2 left_pre right_pre ) ” 
  &&  “ (partitioned_at l1_2 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (right_pre + 1 )) ” 
  &&  “ (right_pre < n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition quicksort_range_partial_solve_wit_3 := quicksort_range_partial_solve_wit_3_pure -> quicksort_range_partial_solve_wit_3_aux.

Definition quicksort_range_partial_solve_wit_4_pure := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 50000)) (PreH12 : (0 <= left_pre)) (PreH13 : (left_pre <= (right_pre + 1 ))) (PreH14 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= (right_pre + 1 )) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (retval <= left_pre)) (PreH11 : (left_pre <= retval)) (PreH12 : (retval <= right_pre)) (PreH13 : (Permutation l l1 )) (PreH14 : (same_outside_range l l1 left_pre right_pre )) (PreH15 : (partitioned_at l1 left_pre right_pre retval )) (PreH16 : (left_pre < right_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 50000)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre <= (right_pre + 1 ))) (PreH22 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ ((Zlength (l1)) = n_pre) ”
).

Definition quicksort_range_partial_solve_wit_4_pure_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (n_pre <= INT_MAX)) (PreH2 : (left_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (retval <= INT_MAX)) (PreH5 : (n_pre >= INT_MIN)) (PreH6 : (left_pre >= INT_MIN)) (PreH7 : (right_pre >= INT_MIN)) (PreH8 : (retval >= INT_MIN)) (PreH9 : (retval < right_pre)) (PreH10 : (retval <= left_pre)) (PreH11 : (left_pre <= retval)) (PreH12 : (retval <= right_pre)) (PreH13 : (Permutation l l1 )) (PreH14 : (same_outside_range l l1 left_pre right_pre )) (PreH15 : (partitioned_at l1 left_pre right_pre retval )) (PreH16 : (left_pre < right_pre)) (PreH17 : ((Zlength (l)) = n_pre)) (PreH18 : (0 <= n_pre)) (PreH19 : (n_pre <= 50000)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre <= (right_pre + 1 ))) (PreH22 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
  **  ((( &( "p" ) )) # Int  |-> retval)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
|--
  “ ((Zlength (l1)) = n_pre) ”
.

Definition quicksort_range_partial_solve_wit_4_aux := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (Permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : (0 <= n_pre)) (PreH11 : (n_pre <= 50000)) (PreH12 : (0 <= left_pre)) (PreH13 : (left_pre <= (right_pre + 1 ))) (PreH14 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) <= (right_pre + 1 )) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ ((Zlength (l1)) = n_pre) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (retval <= left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (Permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (partitioned_at l1 left_pre right_pre retval ) ” 
  &&  “ (left_pre < right_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= (right_pre + 1 )) ” 
  &&  “ (right_pre < n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition quicksort_range_partial_solve_wit_4 := quicksort_range_partial_solve_wit_4_pure -> quicksort_range_partial_solve_wit_4_aux.

(*----- Function dual_loop_quicksort -----*)

Definition dual_loop_quicksort_safety_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : ((Zlength (l)) = n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dual_loop_quicksort_safety_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition dual_loop_quicksort_safety_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition dual_loop_quicksort_safety_wit_4 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition dual_loop_quicksort_return_wit_1 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : (Permutation l l1_2 )) (PreH2 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH3 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH4 : (n_pre > 0)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : (Permutation l l1_2 )) (PreH2 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH3 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH4 : (n_pre > 0)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ ((Zlength (l1_2)) = n_pre) ” 
  &&  “ (increasing l1_2 ) ”
  &&  emp
).

Definition dual_loop_quicksort_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : (Permutation l l1_2 )) (PreH2 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH3 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH4 : (n_pre > 0)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) ,
  ((Zlength (l1_2)) = n_pre)
.

Definition dual_loop_quicksort_return_wit_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : (Permutation l l1_2 )) (PreH2 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH3 : (range_nondecreasing l1_2 0 (n_pre - 1 ) )) (PreH4 : (n_pre > 0)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (0 <= n_pre)) (PreH7 : (n_pre <= 50000)) ,
  (increasing l1_2 )
.

Definition dual_loop_quicksort_return_wit_2 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <= 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ (Permutation l l1 ) ” 
  &&  “ (increasing l1 ) ” 
  &&  “ ((Zlength (l1)) = n_pre) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <= 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ (increasing l ) ” 
  &&  “ (Permutation l l ) ”
  &&  emp
).

Definition dual_loop_quicksort_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <= 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  (increasing l )
.

Definition dual_loop_quicksort_return_wit_2_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (n_pre <= 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  (Permutation l l )
.

Definition dual_loop_quicksort_partial_solve_wit_1_pure := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - 1 ) + 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ”
.

Definition dual_loop_quicksort_partial_solve_wit_1_aux := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (n_pre > 0)) (PreH2 : ((Zlength (l)) = n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 50000)) ,
  (IntArray.full arr_pre n_pre l )
|--
  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - 1 ) + 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ (n_pre > 0) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ”
  &&  (IntArray.full arr_pre n_pre l )
.

Definition dual_loop_quicksort_partial_solve_wit_1 := dual_loop_quicksort_partial_solve_wit_1_pure -> dual_loop_quicksort_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_swap_return_wit_1 : swap_return_wit_1.
Axiom proof_of_swap_partial_solve_wit_1 : swap_partial_solve_wit_1.
Axiom proof_of_swap_partial_solve_wit_2 : swap_partial_solve_wit_2.
Axiom proof_of_swap_partial_solve_wit_3 : swap_partial_solve_wit_3.
Axiom proof_of_swap_partial_solve_wit_4 : swap_partial_solve_wit_4.
Axiom proof_of_partition_two_loop_safety_wit_1 : partition_two_loop_safety_wit_1.
Axiom proof_of_partition_two_loop_safety_wit_2 : partition_two_loop_safety_wit_2.
Axiom proof_of_partition_two_loop_safety_wit_3 : partition_two_loop_safety_wit_3.
Axiom proof_of_partition_two_loop_safety_wit_4 : partition_two_loop_safety_wit_4.
Axiom proof_of_partition_two_loop_entail_wit_1 : partition_two_loop_entail_wit_1.
Axiom proof_of_partition_two_loop_entail_wit_2 : partition_two_loop_entail_wit_2.
Axiom proof_of_partition_two_loop_entail_wit_3 : partition_two_loop_entail_wit_3.
Axiom proof_of_partition_two_loop_entail_wit_4_1 : partition_two_loop_entail_wit_4_1.
Axiom proof_of_partition_two_loop_entail_wit_4_2 : partition_two_loop_entail_wit_4_2.
Axiom proof_of_partition_two_loop_entail_wit_5 : partition_two_loop_entail_wit_5.
Axiom proof_of_partition_two_loop_entail_wit_6_1 : partition_two_loop_entail_wit_6_1.
Axiom proof_of_partition_two_loop_entail_wit_6_2 : partition_two_loop_entail_wit_6_2.
Axiom proof_of_partition_two_loop_return_wit_1 : partition_two_loop_return_wit_1.
Axiom proof_of_partition_two_loop_partial_solve_wit_1 : partition_two_loop_partial_solve_wit_1.
Axiom proof_of_partition_two_loop_partial_solve_wit_2 : partition_two_loop_partial_solve_wit_2.
Axiom proof_of_partition_two_loop_partial_solve_wit_3 : partition_two_loop_partial_solve_wit_3.
Axiom proof_of_partition_two_loop_partial_solve_wit_4_pure : partition_two_loop_partial_solve_wit_4_pure.
Axiom proof_of_partition_two_loop_partial_solve_wit_4 : partition_two_loop_partial_solve_wit_4.
Axiom proof_of_partition_two_loop_partial_solve_wit_5_pure : partition_two_loop_partial_solve_wit_5_pure.
Axiom proof_of_partition_two_loop_partial_solve_wit_5 : partition_two_loop_partial_solve_wit_5.
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
Axiom proof_of_dual_loop_quicksort_safety_wit_1 : dual_loop_quicksort_safety_wit_1.
Axiom proof_of_dual_loop_quicksort_safety_wit_2 : dual_loop_quicksort_safety_wit_2.
Axiom proof_of_dual_loop_quicksort_safety_wit_3 : dual_loop_quicksort_safety_wit_3.
Axiom proof_of_dual_loop_quicksort_safety_wit_4 : dual_loop_quicksort_safety_wit_4.
Axiom proof_of_dual_loop_quicksort_return_wit_1 : dual_loop_quicksort_return_wit_1.
Axiom proof_of_dual_loop_quicksort_return_wit_2 : dual_loop_quicksort_return_wit_2.
Axiom proof_of_dual_loop_quicksort_partial_solve_wit_1_pure : dual_loop_quicksort_partial_solve_wit_1_pure.
Axiom proof_of_dual_loop_quicksort_partial_solve_wit_1 : dual_loop_quicksort_partial_solve_wit_1.

End VC_Correct.
