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
Require Import SimpleC.EE.LLM_bench.Algorithms.discretize.discretize_lib.
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
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
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ ((Znth high_pre l 0) = (Znth (high_pre) (l) (0))) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (low_pre - 1 )) ” 
  &&  “ ((low_pre - 1 ) < low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (partition_scan_inv l l1 low_pre high_pre (Znth high_pre l 0) (low_pre - 1 ) low_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  TT && emp 
|--
  “ (partition_scan_inv l l low_pre high_pre (Znth high_pre l 0) (low_pre - 1 ) low_pre ) ”
  &&  emp
).

Definition partition_entail_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) ,
  (partition_scan_inv l l low_pre high_pre (Znth high_pre l 0) (low_pre - 1 ) low_pre )
.

Definition partition_entail_wit_2_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre (replace_Znth (j) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (j) (l1_2) (0))) (l1_2)))) )
|--
  EX (l1: (@list Z)) ,
  “ (pivot = (Znth (high_pre) (l) (0))) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ (partition_scan_inv l l1 low_pre high_pre pivot (i + 1 ) (j + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partition_scan_inv l (replace_Znth (j) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (j) (l1_2) (0))) (l1_2)))) low_pre high_pre pivot (i + 1 ) (j + 1 ) ) ”
  &&  emp
).

Definition partition_entail_wit_2_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partition_scan_inv l (replace_Znth (j) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (j) (l1_2) (0))) (l1_2)))) low_pre high_pre pivot (i + 1 ) (j + 1 ) )
.

Definition partition_entail_wit_2_2 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (pivot = (Znth (high_pre) (l) (0))) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < (j + 1 )) ” 
  &&  “ ((j + 1 ) <= high_pre) ” 
  &&  “ (partition_scan_inv l l1 low_pre high_pre pivot i (j + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partition_scan_inv l l1_2 low_pre high_pre pivot i (j + 1 ) ) ”
  &&  emp
).

Definition partition_entail_wit_2_2_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1_2 0) > pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partition_scan_inv l l1_2 low_pre high_pre pivot i (j + 1 ) )
.

Definition partition_return_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))) )
|--
  EX (l1: (@list Z)) ,
  “ (low_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= high_pre) ” 
  &&  “ (permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 low_pre high_pre ) ” 
  &&  “ (partitioned_at l1 low_pre high_pre (i + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  TT && emp 
|--
  “ (partitioned_at (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))) low_pre high_pre (i + 1 ) ) ” 
  &&  “ (same_outside_range l (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))) low_pre high_pre ) ” 
  &&  “ (permutation l (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))) ) ”
  &&  emp
).

Definition partition_return_wit_1_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (partitioned_at (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))) low_pre high_pre (i + 1 ) )
.

Definition partition_return_wit_1_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (same_outside_range l (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))) low_pre high_pre )
.

Definition partition_return_wit_1_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1_2 low_pre high_pre pivot i j )) ,
  (permutation l (replace_Znth (high_pre) ((Znth ((i + 1 )) (l1_2) (0))) ((replace_Znth ((i + 1 )) ((Znth (high_pre) (l1_2) (0))) (l1_2)))) )
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j < high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (j < high_pre) ” 
  &&  “ (pivot = (Znth (high_pre) (l) (0))) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_scan_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (((arr_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l1 0))
  **  (IntArray.missing_i arr_pre j 0 n_pre l1 )
.

Definition partition_partial_solve_wit_3_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : ((Znth j l1 0) <= pivot)) (PreH2 : (j < high_pre)) (PreH3 : (pivot = (Znth (high_pre) (l) (0)))) (PreH4 : (0 <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((low_pre - 1 ) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((Znth j l1 0) <= pivot) ” 
  &&  “ (j < high_pre) ” 
  &&  “ (pivot = (Znth (high_pre) (l) (0))) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_scan_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition partition_partial_solve_wit_3 := partition_partial_solve_wit_3_pure -> partition_partial_solve_wit_3_aux.

Definition partition_partial_solve_wit_4_pure := 
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
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
forall (high_pre: Z) (low_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (j: Z) (i: Z) (pivot: Z) (PreH1 : (j >= high_pre)) (PreH2 : (pivot = (Znth (high_pre) (l) (0)))) (PreH3 : (0 <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((low_pre - 1 ) <= i)) (PreH7 : (i < j)) (PreH8 : (j <= high_pre)) (PreH9 : (partition_scan_inv l l1 low_pre high_pre pivot i j )) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) < n_pre) ” 
  &&  “ (0 <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ (j >= high_pre) ” 
  &&  “ (pivot = (Znth (high_pre) (l) (0))) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (high_pre < n_pre) ” 
  &&  “ ((low_pre - 1 ) <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j <= high_pre) ” 
  &&  “ (partition_scan_inv l l1 low_pre high_pre pivot i j ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
.

Definition partition_partial_solve_wit_4 := partition_partial_solve_wit_4_pure -> partition_partial_solve_wit_4_aux.

(*----- Function quicksort_range -----*)

Definition quicksort_range_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (sorted_range l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (sorted_range l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (0 <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_4 )
|--
  EX (l1: (@list Z)) ,
  “ (permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (sorted_range l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (0 <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (sorted_range l1_4 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_4 left_pre right_pre ) ” 
  &&  “ (permutation l l1_4 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (0 <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (sorted_range l1_4 left_pre right_pre )
.

Definition quicksort_range_return_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (0 <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (same_outside_range l l1_4 left_pre right_pre )
.

Definition quicksort_range_return_wit_1_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (l1_4: (@list Z)) (PreH1 : (permutation l1_3 l1_4 )) (PreH2 : (same_outside_range l1_3 l1_4 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_4 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (permutation l1_2 l1_3 )) (PreH6 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH7 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH8 : (retval > left_pre)) (PreH9 : (left_pre <= retval)) (PreH10 : (retval <= right_pre)) (PreH11 : (permutation l l1_2 )) (PreH12 : (same_outside_range l l1_2 left_pre right_pre )) (PreH13 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH14 : (left_pre < right_pre)) (PreH15 : (0 <= n_pre)) (PreH16 : (0 <= left_pre)) (PreH17 : ((-1) <= right_pre)) (PreH18 : (right_pre < n_pre)) ,
  (permutation l l1_4 )
.

Definition quicksort_range_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_3 )
|--
  EX (l1: (@list Z)) ,
  “ (permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (sorted_range l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (sorted_range l1_3 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_3 left_pre right_pre ) ” 
  &&  “ (permutation l l1_3 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (sorted_range l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_2_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_2_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (permutation l1_2 l1_3 )) (PreH2 : (same_outside_range l1_2 l1_3 (retval + 1 ) right_pre )) (PreH3 : (sorted_range l1_3 (retval + 1 ) right_pre )) (PreH4 : (retval < right_pre)) (PreH5 : (retval <= left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (permutation l l1_3 )
.

Definition quicksort_range_return_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_3 )
|--
  EX (l1: (@list Z)) ,
  “ (permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (sorted_range l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (sorted_range l1_3 left_pre right_pre ) ” 
  &&  “ (same_outside_range l l1_3 left_pre right_pre ) ” 
  &&  “ (permutation l l1_3 ) ”
  &&  emp
).

Definition quicksort_range_return_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (sorted_range l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_3_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (same_outside_range l l1_3 left_pre right_pre )
.

Definition quicksort_range_return_wit_3_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (retval: Z) (l1_3: (@list Z)) (PreH1 : (retval >= right_pre)) (PreH2 : (permutation l1_2 l1_3 )) (PreH3 : (same_outside_range l1_2 l1_3 left_pre (retval - 1 ) )) (PreH4 : (sorted_range l1_3 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1_2 )) (PreH9 : (same_outside_range l l1_2 left_pre right_pre )) (PreH10 : (partitioned_at l1_2 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (permutation l l1_3 )
.

Definition quicksort_range_return_wit_4 := 
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l )
|--
  EX (l1: (@list Z)) ,
  “ (permutation l l1 ) ” 
  &&  “ (same_outside_range l l1 left_pre right_pre ) ” 
  &&  “ (sorted_range l1 left_pre right_pre ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  TT && emp 
|--
  “ (sorted_range l left_pre right_pre ) ” 
  &&  “ (same_outside_range l l left_pre right_pre ) ” 
  &&  “ (permutation l l ) ”
  &&  emp
).

Definition quicksort_range_return_wit_4_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (sorted_range l left_pre right_pre )
.

Definition quicksort_range_return_wit_4_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (same_outside_range l l left_pre right_pre )
.

Definition quicksort_range_return_wit_4_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (left_pre >= right_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= left_pre)) (PreH4 : ((-1) <= right_pre)) (PreH5 : (right_pre < n_pre)) ,
  (permutation l l )
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (permutation l l1 )) (PreH5 : (same_outside_range l l1 left_pre right_pre )) (PreH6 : (partitioned_at l1 left_pre right_pre retval )) (PreH7 : (left_pre < right_pre)) (PreH8 : (0 <= n_pre)) (PreH9 : (0 <= left_pre)) (PreH10 : ((-1) <= right_pre)) (PreH11 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ ((-1) <= (retval - 1 )) ” 
  &&  “ ((retval - 1 ) < n_pre) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (permutation l l1 ) ” 
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (sorted_range l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (l1_2: (@list Z)) (PreH1 : (retval < right_pre)) (PreH2 : (permutation l1 l1_2 )) (PreH3 : (same_outside_range l1 l1_2 left_pre (retval - 1 ) )) (PreH4 : (sorted_range l1_2 left_pre (retval - 1 ) )) (PreH5 : (retval > left_pre)) (PreH6 : (left_pre <= retval)) (PreH7 : (retval <= right_pre)) (PreH8 : (permutation l l1 )) (PreH9 : (same_outside_range l l1 left_pre right_pre )) (PreH10 : (partitioned_at l1 left_pre right_pre retval )) (PreH11 : (left_pre < right_pre)) (PreH12 : (0 <= n_pre)) (PreH13 : (0 <= left_pre)) (PreH14 : ((-1) <= right_pre)) (PreH15 : (right_pre < n_pre)) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= (retval + 1 )) ” 
  &&  “ ((-1) <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (retval < right_pre) ” 
  &&  “ (permutation l1 l1_2 ) ” 
  &&  “ (same_outside_range l1 l1_2 left_pre (retval - 1 ) ) ” 
  &&  “ (sorted_range l1_2 left_pre (retval - 1 ) ) ” 
  &&  “ (retval > left_pre) ” 
  &&  “ (left_pre <= retval) ” 
  &&  “ (retval <= right_pre) ” 
  &&  “ (permutation l l1 ) ” 
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
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
forall (right_pre: Z) (left_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1: (@list Z)) (retval: Z) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (permutation l l1 )) (PreH6 : (same_outside_range l l1 left_pre right_pre )) (PreH7 : (partitioned_at l1 left_pre right_pre retval )) (PreH8 : (left_pre < right_pre)) (PreH9 : (0 <= n_pre)) (PreH10 : (0 <= left_pre)) (PreH11 : ((-1) <= right_pre)) (PreH12 : (right_pre < n_pre)) ,
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
  &&  “ (permutation l l1 ) ” 
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

(*----- Function int_array_quicksort -----*)

Definition int_array_quicksort_safety_wit_1 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition int_array_quicksort_safety_wit_2 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition int_array_quicksort_safety_wit_3 := 
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 50000)) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition int_array_quicksort_return_wit_1 := 
(
forall (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : (permutation l l1_2 )) (PreH2 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH3 : (sorted_range l1_2 0 (n_pre - 1 ) )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  (IntArray.full arr_pre n_pre l1_2 )
|--
  EX (l1: (@list Z)) ,
  “ (permutation l l1 ) ” 
  &&  “ (increasing l1 ) ”
  &&  (IntArray.full arr_pre n_pre l1 )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : (permutation l l1_2 )) (PreH2 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH3 : (sorted_range l1_2 0 (n_pre - 1 ) )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ (increasing l1_2 ) ”
  &&  emp
).

Definition int_array_quicksort_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (l1_2: (@list Z)) (PreH1 : (permutation l l1_2 )) (PreH2 : (same_outside_range l l1_2 0 (n_pre - 1 ) )) (PreH3 : (sorted_range l1_2 0 (n_pre - 1 ) )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  (increasing l1_2 )
.

Definition int_array_quicksort_partial_solve_wit_1_pure := 
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

Definition int_array_quicksort_partial_solve_wit_1_aux := 
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

Definition int_array_quicksort_partial_solve_wit_1 := int_array_quicksort_partial_solve_wit_1_pure -> int_array_quicksort_partial_solve_wit_1_aux.

(*----- Function discretize -----*)

Definition discretize_safety_wit_1 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.undef_full dest_map_pre n_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition discretize_safety_wit_2 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (IntArray.full dest_map_pre (i + 1 ) (app ((sublist (0) (i) (src_l))) ((cons ((Znth i src_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dest_map_pre (i + 1 ) n_pre )
  **  (IntArray.full src_pre n_pre src_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition discretize_safety_wit_3 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (l1: (@list Z)) (PreH1 : (permutation src_l l1 )) (PreH2 : (increasing l1 )) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  ((( &( "slow" ) )) # Int  |->_)
  **  (IntArray.full dest_map_pre n_pre l1 )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full src_pre n_pre src_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition discretize_safety_wit_4 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (l1: (@list Z)) (PreH1 : (permutation src_l l1 )) (PreH2 : (increasing l1 )) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  ((( &( "fast" ) )) # Int  |->_)
  **  ((( &( "slow" ) )) # Int  |-> 0)
  **  (IntArray.full dest_map_pre n_pre l1 )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full src_pre n_pre src_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition discretize_safety_wit_5 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : ((Znth fast cur_l 0) <> (Znth slow cur_l 0))) (PreH2 : (fast < n_pre)) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= slow)) (PreH7 : (slow < fast)) (PreH8 : (1 <= fast)) (PreH9 : (fast <= n_pre)) (PreH10 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  (IntArray.full dest_map_pre n_pre cur_l )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "slow" ) )) # Int  |-> slow)
  **  ((( &( "fast" ) )) # Int  |-> fast)
  **  (IntArray.full src_pre n_pre src_l )
|--
  “ ((slow + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (slow + 1 )) ”
.

Definition discretize_safety_wit_6 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : ((Znth fast cur_l 0) <> (Znth slow cur_l 0))) (PreH2 : (fast < n_pre)) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= slow)) (PreH7 : (slow < fast)) (PreH8 : (1 <= fast)) (PreH9 : (fast <= n_pre)) (PreH10 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  (IntArray.full dest_map_pre n_pre (replace_Znth ((slow + 1 )) ((Znth fast cur_l 0)) (cur_l)) )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "slow" ) )) # Int  |-> (slow + 1 ))
  **  ((( &( "fast" ) )) # Int  |-> fast)
  **  (IntArray.full src_pre n_pre src_l )
|--
  “ ((fast + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fast + 1 )) ”
.

Definition discretize_safety_wit_7 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : ((Znth fast cur_l 0) = (Znth slow cur_l 0))) (PreH2 : (fast < n_pre)) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= slow)) (PreH7 : (slow < fast)) (PreH8 : (1 <= fast)) (PreH9 : (fast <= n_pre)) (PreH10 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  (IntArray.full dest_map_pre n_pre cur_l )
  **  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "slow" ) )) # Int  |-> slow)
  **  ((( &( "fast" ) )) # Int  |-> fast)
  **  (IntArray.full src_pre n_pre src_l )
|--
  “ ((fast + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fast + 1 )) ”
.

Definition discretize_safety_wit_8 := 
(
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (out_l: (@list Z)) (slow: Z) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (discretize_result src_l n_pre out_l (slow + 1 ) )) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "slow" ) )) # Int  |-> slow)
  **  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre out_l )
|--
  “ ((slow + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (slow + 1 )) ”
) \/
(
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (out_l: (@list Z)) (slow: Z) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (discretize_result src_l n_pre out_l (slow + 1 ) )) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "slow" ) )) # Int  |-> slow)
  **  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre out_l )
|--
  “ ((slow + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (slow + 1 )) ”
).

Definition discretize_safety_wit_8_split_goal_1 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (out_l: (@list Z)) (slow: Z) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (discretize_result src_l n_pre out_l (slow + 1 ) )) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "slow" ) )) # Int  |-> slow)
  **  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre out_l )
|--
  “ ((slow + 1 ) <= INT_MAX) ”
.

Definition discretize_safety_wit_8_split_goal_2 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (out_l: (@list Z)) (slow: Z) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (discretize_result src_l n_pre out_l (slow + 1 ) )) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "slow" ) )) # Int  |-> slow)
  **  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre out_l )
|--
  “ ((INT_MIN) <= (slow + 1 )) ”
.

Definition discretize_safety_wit_9 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (out_l: (@list Z)) (slow: Z) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (discretize_result src_l n_pre out_l (slow + 1 ) )) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "slow" ) )) # Int  |-> slow)
  **  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre out_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition discretize_entail_wit_1 := 
(
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.undef_full dest_map_pre n_pre )
|--
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ”
  &&  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre 0 (sublist (0) (0) (src_l)) )
  **  (IntArray.undef_seg dest_map_pre 0 n_pre )
) \/
(
forall (n_pre: Z) (src_l: (@list Z)) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  TT && emp 
|--
  “ ((sublist (0) (0) (src_l)) = (@nil Z)) ”
  &&  emp
).

Definition discretize_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (src_l: (@list Z)) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  ((sublist (0) (0) (src_l)) = (@nil Z))
.

Definition discretize_entail_wit_2 := 
(
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (IntArray.full dest_map_pre (i + 1 ) (app ((sublist (0) (i) (src_l))) ((cons ((Znth i src_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dest_map_pre (i + 1 ) n_pre )
  **  (IntArray.full src_pre n_pre src_l )
|--
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ”
  &&  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre (i + 1 ) (sublist (0) ((i + 1 )) (src_l)) )
  **  (IntArray.undef_seg dest_map_pre (i + 1 ) n_pre )
) \/
(
forall (n_pre: Z) (src_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  TT && emp 
|--
  “ ((app ((sublist (0) (i) (src_l))) ((cons ((Znth i src_l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (src_l))) ”
  &&  emp
).

Definition discretize_entail_wit_2_split_goal_1 := 
forall (n_pre: Z) (src_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  ((app ((sublist (0) (i) (src_l))) ((cons ((Znth i src_l 0)) ((@nil Z))))) = (sublist (0) ((i + 1 )) (src_l)))
.

Definition discretize_entail_wit_3 := 
(
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre i (sublist (0) (i) (src_l)) )
  **  (IntArray.undef_seg dest_map_pre i n_pre )
|--
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ”
  &&  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre src_l )
) \/
(
forall (dest_map_pre: Z) (n_pre: Z) (src_l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (IntArray.full dest_map_pre i (sublist (0) (i) (src_l)) )
|--
  (IntArray.full dest_map_pre n_pre src_l )
).

Definition discretize_entail_wit_3_split_goal_spatial := 
forall (dest_map_pre: Z) (n_pre: Z) (src_l: (@list Z)) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (IntArray.full dest_map_pre i (sublist (0) (i) (src_l)) )
|--
  (IntArray.full dest_map_pre n_pre src_l )
.

Definition discretize_entail_wit_4 := 
(
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (l1: (@list Z)) (PreH1 : (permutation src_l l1 )) (PreH2 : (increasing l1 )) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  (IntArray.full dest_map_pre n_pre l1 )
  **  (IntArray.full src_pre n_pre src_l )
|--
  EX (sorted_l: (@list Z))  (cur_l: (@list Z)) ,
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l cur_l 0 1 ) ”
  &&  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre cur_l )
) \/
(
forall (n_pre: Z) (src_l: (@list Z)) (l1: (@list Z)) (PreH1 : (permutation src_l l1 )) (PreH2 : (increasing l1 )) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) ,
  TT && emp 
|--
  EX (sorted_l: (@list Z)) ,
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l l1 0 1 ) ”
  &&  emp
).

Definition discretize_entail_wit_5_1 := 
(
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l_2: (@list Z)) (cur_l_2: (@list Z)) (fast: Z) (slow: Z) (PreH1 : ((Znth fast cur_l_2 0) <> (Znth slow cur_l_2 0))) (PreH2 : (fast < n_pre)) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= slow)) (PreH7 : (slow < fast)) (PreH8 : (1 <= fast)) (PreH9 : (fast <= n_pre)) (PreH10 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast )) ,
  (IntArray.full dest_map_pre n_pre (replace_Znth ((slow + 1 )) ((Znth fast cur_l_2 0)) (cur_l_2)) )
  **  (IntArray.full src_pre n_pre src_l )
|--
  EX (sorted_l: (@list Z))  (cur_l: (@list Z)) ,
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (slow + 1 )) ” 
  &&  “ ((slow + 1 ) < (fast + 1 )) ” 
  &&  “ (1 <= (fast + 1 )) ” 
  &&  “ ((fast + 1 ) <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l cur_l (slow + 1 ) (fast + 1 ) ) ”
  &&  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre cur_l )
) \/
(
forall (n_pre: Z) (src_l: (@list Z)) (sorted_l_2: (@list Z)) (cur_l_2: (@list Z)) (fast: Z) (slow: Z) (PreH1 : ((Znth fast cur_l_2 0) <> (Znth slow cur_l_2 0))) (PreH2 : (fast < n_pre)) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= slow)) (PreH7 : (slow < fast)) (PreH8 : (1 <= fast)) (PreH9 : (fast <= n_pre)) (PreH10 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast )) ,
  TT && emp 
|--
  EX (sorted_l: (@list Z)) ,
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= (slow + 1 )) ” 
  &&  “ ((slow + 1 ) < (fast + 1 )) ” 
  &&  “ (1 <= (fast + 1 )) ” 
  &&  “ ((fast + 1 ) <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l (replace_Znth ((slow + 1 )) ((Znth fast cur_l_2 0)) (cur_l_2)) (slow + 1 ) (fast + 1 ) ) ”
  &&  emp
).

Definition discretize_entail_wit_5_2 := 
(
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l_2: (@list Z)) (cur_l_2: (@list Z)) (fast: Z) (slow: Z) (PreH1 : ((Znth fast cur_l_2 0) = (Znth slow cur_l_2 0))) (PreH2 : (fast < n_pre)) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= slow)) (PreH7 : (slow < fast)) (PreH8 : (1 <= fast)) (PreH9 : (fast <= n_pre)) (PreH10 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast )) ,
  (IntArray.full dest_map_pre n_pre cur_l_2 )
  **  (IntArray.full src_pre n_pre src_l )
|--
  EX (sorted_l: (@list Z))  (cur_l: (@list Z)) ,
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= slow) ” 
  &&  “ (slow < (fast + 1 )) ” 
  &&  “ (1 <= (fast + 1 )) ” 
  &&  “ ((fast + 1 ) <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l cur_l slow (fast + 1 ) ) ”
  &&  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre cur_l )
) \/
(
forall (n_pre: Z) (src_l: (@list Z)) (sorted_l_2: (@list Z)) (cur_l_2: (@list Z)) (fast: Z) (slow: Z) (PreH1 : ((Znth fast cur_l_2 0) = (Znth slow cur_l_2 0))) (PreH2 : (fast < n_pre)) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= slow)) (PreH7 : (slow < fast)) (PreH8 : (1 <= fast)) (PreH9 : (fast <= n_pre)) (PreH10 : (dedup_scan_inv src_l sorted_l_2 cur_l_2 slow fast )) ,
  TT && emp 
|--
  EX (sorted_l: (@list Z)) ,
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= slow) ” 
  &&  “ (slow < (fast + 1 )) ” 
  &&  “ (1 <= (fast + 1 )) ” 
  &&  “ ((fast + 1 ) <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l cur_l_2 slow (fast + 1 ) ) ”
  &&  emp
).

Definition discretize_entail_wit_6 := 
(
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : (fast >= n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= slow)) (PreH6 : (slow < fast)) (PreH7 : (1 <= fast)) (PreH8 : (fast <= n_pre)) (PreH9 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre cur_l )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (discretize_result src_l n_pre out_l (slow + 1 ) ) ”
  &&  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre out_l )
) \/
(
forall (n_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : (fast >= n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= slow)) (PreH6 : (slow < fast)) (PreH7 : (1 <= fast)) (PreH8 : (fast <= n_pre)) (PreH9 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  TT && emp 
|--
  “ (discretize_result src_l n_pre cur_l (slow + 1 ) ) ”
  &&  emp
).

Definition discretize_entail_wit_6_split_goal_1 := 
forall (n_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : (fast >= n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= slow)) (PreH6 : (slow < fast)) (PreH7 : (1 <= fast)) (PreH8 : (fast <= n_pre)) (PreH9 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  (discretize_result src_l n_pre cur_l (slow + 1 ) )
.

Definition discretize_return_wit_1 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (out_l_2: (@list Z)) (slow: Z) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : (discretize_result src_l n_pre out_l_2 (slow + 1 ) )) ,
  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre out_l_2 )
|--
  EX (out_l: (@list Z)) ,
  “ (discretize_result src_l n_pre out_l (slow + 1 ) ) ”
  &&  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre out_l )
.

Definition discretize_partial_solve_wit_1 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre i (sublist (0) (i) (src_l)) )
  **  (IntArray.undef_seg dest_map_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((src_pre + (i * sizeof(INT)))) # Int  |-> (Znth i src_l 0))
  **  (IntArray.missing_i src_pre i 0 n_pre src_l )
  **  (IntArray.full dest_map_pre i (sublist (0) (i) (src_l)) )
  **  (IntArray.undef_seg dest_map_pre i n_pre )
.

Definition discretize_partial_solve_wit_2 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= i)) (PreH6 : (i <= n_pre)) ,
  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre i (sublist (0) (i) (src_l)) )
  **  (IntArray.undef_seg dest_map_pre i n_pre )
|--
  “ (i < n_pre) ” 
  &&  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ”
  &&  (((dest_map_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dest_map_pre (i + 1 ) n_pre )
  **  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre i (sublist (0) (i) (src_l)) )
.

Definition discretize_partial_solve_wit_3_pure := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  ((( &( "src" ) )) # Ptr  |-> src_pre)
  **  ((( &( "dest_map" ) )) # Ptr  |-> dest_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre src_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ”
.

Definition discretize_partial_solve_wit_3_aux := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (PreH1 : ((Zlength (src_l)) = n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 50000)) ,
  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre src_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ”
  &&  (IntArray.full dest_map_pre n_pre src_l )
  **  (IntArray.full src_pre n_pre src_l )
.

Definition discretize_partial_solve_wit_3 := discretize_partial_solve_wit_3_pure -> discretize_partial_solve_wit_3_aux.

Definition discretize_partial_solve_wit_4 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : (fast < n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= slow)) (PreH6 : (slow < fast)) (PreH7 : (1 <= fast)) (PreH8 : (fast <= n_pre)) (PreH9 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  (IntArray.full src_pre n_pre src_l )
  **  (IntArray.full dest_map_pre n_pre cur_l )
|--
  “ (fast < n_pre) ” 
  &&  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= slow) ” 
  &&  “ (slow < fast) ” 
  &&  “ (1 <= fast) ” 
  &&  “ (fast <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l cur_l slow fast ) ”
  &&  (((dest_map_pre + (fast * sizeof(INT)))) # Int  |-> (Znth fast cur_l 0))
  **  (IntArray.missing_i dest_map_pre fast 0 n_pre cur_l )
  **  (IntArray.full src_pre n_pre src_l )
.

Definition discretize_partial_solve_wit_5 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : (fast < n_pre)) (PreH2 : ((Zlength (src_l)) = n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : (0 <= slow)) (PreH6 : (slow < fast)) (PreH7 : (1 <= fast)) (PreH8 : (fast <= n_pre)) (PreH9 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  (IntArray.full dest_map_pre n_pre cur_l )
  **  (IntArray.full src_pre n_pre src_l )
|--
  “ (fast < n_pre) ” 
  &&  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= slow) ” 
  &&  “ (slow < fast) ” 
  &&  “ (1 <= fast) ” 
  &&  “ (fast <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l cur_l slow fast ) ”
  &&  (((dest_map_pre + (slow * sizeof(INT)))) # Int  |-> (Znth slow cur_l 0))
  **  (IntArray.missing_i dest_map_pre slow 0 n_pre cur_l )
  **  (IntArray.full src_pre n_pre src_l )
.

Definition discretize_partial_solve_wit_6 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : ((Znth fast cur_l 0) <> (Znth slow cur_l 0))) (PreH2 : (fast < n_pre)) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= slow)) (PreH7 : (slow < fast)) (PreH8 : (1 <= fast)) (PreH9 : (fast <= n_pre)) (PreH10 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  (IntArray.full dest_map_pre n_pre cur_l )
  **  (IntArray.full src_pre n_pre src_l )
|--
  “ ((Znth fast cur_l 0) <> (Znth slow cur_l 0)) ” 
  &&  “ (fast < n_pre) ” 
  &&  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= slow) ” 
  &&  “ (slow < fast) ” 
  &&  “ (1 <= fast) ” 
  &&  “ (fast <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l cur_l slow fast ) ”
  &&  (((dest_map_pre + (fast * sizeof(INT)))) # Int  |-> (Znth fast cur_l 0))
  **  (IntArray.missing_i dest_map_pre fast 0 n_pre cur_l )
  **  (IntArray.full src_pre n_pre src_l )
.

Definition discretize_partial_solve_wit_7 := 
forall (dest_map_pre: Z) (n_pre: Z) (src_pre: Z) (src_l: (@list Z)) (sorted_l: (@list Z)) (cur_l: (@list Z)) (fast: Z) (slow: Z) (PreH1 : ((Znth fast cur_l 0) <> (Znth slow cur_l 0))) (PreH2 : (fast < n_pre)) (PreH3 : ((Zlength (src_l)) = n_pre)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : (0 <= slow)) (PreH7 : (slow < fast)) (PreH8 : (1 <= fast)) (PreH9 : (fast <= n_pre)) (PreH10 : (dedup_scan_inv src_l sorted_l cur_l slow fast )) ,
  (IntArray.full dest_map_pre n_pre cur_l )
  **  (IntArray.full src_pre n_pre src_l )
|--
  “ ((Znth fast cur_l 0) <> (Znth slow cur_l 0)) ” 
  &&  “ (fast < n_pre) ” 
  &&  “ ((Zlength (src_l)) = n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 50000) ” 
  &&  “ (0 <= slow) ” 
  &&  “ (slow < fast) ” 
  &&  “ (1 <= fast) ” 
  &&  “ (fast <= n_pre) ” 
  &&  “ (dedup_scan_inv src_l sorted_l cur_l slow fast ) ”
  &&  (((dest_map_pre + ((slow + 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dest_map_pre (slow + 1 ) 0 n_pre cur_l )
  **  (IntArray.full src_pre n_pre src_l )
.

(*----- Function query_forward -----*)

Definition query_forward_safety_wit_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) ,
  ((( &( "low" ) )) # Int  |->_)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition query_forward_safety_wit_2 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) ,
  ((( &( "high" ) )) # Int  |->_)
  **  ((( &( "low" ) )) # Int  |-> 0)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((map_size_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (map_size_pre - 1 )) ”
.

Definition query_forward_safety_wit_3 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) ,
  ((( &( "high" ) )) # Int  |->_)
  **  ((( &( "low" ) )) # Int  |-> 0)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_forward_safety_wit_4 := 
(
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((low + ((high - low ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low + ((high - low ) ÷ 2 ) )) ”
) \/
(
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((low + ((high - low ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low + ((high - low ) ÷ 2 ) )) ”
).

Definition query_forward_safety_wit_4_split_goal_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((low + ((high - low ) ÷ 2 ) ) <= INT_MAX) ”
.

Definition query_forward_safety_wit_4_split_goal_2 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((INT_MIN) <= (low + ((high - low ) ÷ 2 ) )) ”
.

Definition query_forward_safety_wit_5 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ (((high - low ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition query_forward_safety_wit_6 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((high - low ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (high - low )) ”
.

Definition query_forward_safety_wit_7 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  ((( &( "mid" ) )) # Int  |->_)
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_forward_safety_wit_8 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) < target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "high" ) )) # Int  |-> high)
|--
  “ ((mid + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (mid + 1 )) ”
.

Definition query_forward_safety_wit_9 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) < target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "high" ) )) # Int  |-> high)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_forward_safety_wit_10 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) >= target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "high" ) )) # Int  |-> high)
|--
  “ ((mid - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (mid - 1 )) ”
.

Definition query_forward_safety_wit_11 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) >= target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
  **  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "mid" ) )) # Int  |-> mid)
  **  ((( &( "high" ) )) # Int  |-> high)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_forward_safety_wit_12 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (high: Z) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) (PreH5 : (0 <= low)) (PreH6 : (low <= (high + 1 ))) (PreH7 : (high < map_size_pre)) (PreH8 : (query_forward_search_inv map_l map_size_pre target_pre low high )) (PreH9 : (query_forward_result map_l map_size_pre target_pre (-1) )) ,
  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition query_forward_safety_wit_13 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (high: Z) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) (PreH5 : (0 <= low)) (PreH6 : (low <= (high + 1 ))) (PreH7 : (high < map_size_pre)) (PreH8 : (query_forward_search_inv map_l map_size_pre target_pre low high )) (PreH9 : (query_forward_result map_l map_size_pre target_pre (-1) )) ,
  ((( &( "map" ) )) # Ptr  |-> map_pre)
  **  ((( &( "map_size" ) )) # Int  |-> map_size_pre)
  **  ((( &( "target" ) )) # Int  |-> target_pre)
  **  ((( &( "low" ) )) # Int  |-> low)
  **  ((( &( "high" ) )) # Int  |-> high)
  **  (IntArray.full map_pre map_size_pre map_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_forward_entail_wit_1 := 
(
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) ,
  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((Zlength (map_l)) = map_size_pre) ” 
  &&  “ (0 <= map_size_pre) ” 
  &&  “ (map_size_pre <= 50000) ” 
  &&  “ (strict_increasing map_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((map_size_pre - 1 ) + 1 )) ” 
  &&  “ ((map_size_pre - 1 ) < map_size_pre) ” 
  &&  “ (query_forward_search_inv map_l map_size_pre target_pre 0 (map_size_pre - 1 ) ) ”
  &&  (IntArray.full map_pre map_size_pre map_l )
) \/
(
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) ,
  TT && emp 
|--
  “ (query_forward_search_inv map_l map_size_pre target_pre 0 (map_size_pre - 1 ) ) ”
  &&  emp
).

Definition query_forward_entail_wit_1_split_goal_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) ,
  (query_forward_search_inv map_l map_size_pre target_pre 0 (map_size_pre - 1 ) )
.

Definition query_forward_entail_wit_2 := 
(
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((Zlength (map_l)) = map_size_pre) ” 
  &&  “ (0 <= map_size_pre) ” 
  &&  “ (map_size_pre <= 50000) ” 
  &&  “ (strict_increasing map_l ) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= (low + ((high - low ) ÷ 2 ) )) ” 
  &&  “ ((low + ((high - low ) ÷ 2 ) ) <= high) ” 
  &&  “ (high < map_size_pre) ” 
  &&  “ (query_forward_search_inv map_l map_size_pre target_pre low high ) ”
  &&  (IntArray.full map_pre map_size_pre map_l )
) \/
(
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  TT && emp 
|--
  “ ((low + ((high - low ) ÷ 2 ) ) <= high) ” 
  &&  “ (low <= (low + ((high - low ) ÷ 2 ) )) ”
  &&  emp
).

Definition query_forward_entail_wit_2_split_goal_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  ((low + ((high - low ) ÷ 2 ) ) <= high)
.

Definition query_forward_entail_wit_2_split_goal_2 := 
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low <= high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (low <= (low + ((high - low ) ÷ 2 ) ))
.

Definition query_forward_entail_wit_3_1 := 
(
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) < target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((Zlength (map_l)) = map_size_pre) ” 
  &&  “ (0 <= map_size_pre) ” 
  &&  “ (map_size_pre <= 50000) ” 
  &&  “ (strict_increasing map_l ) ” 
  &&  “ (0 <= (mid + 1 )) ” 
  &&  “ ((mid + 1 ) <= (high + 1 )) ” 
  &&  “ (high < map_size_pre) ” 
  &&  “ (query_forward_search_inv map_l map_size_pre target_pre (mid + 1 ) high ) ”
  &&  (IntArray.full map_pre map_size_pre map_l )
) \/
(
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) < target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  TT && emp 
|--
  “ (query_forward_search_inv map_l map_size_pre target_pre (mid + 1 ) high ) ”
  &&  emp
).

Definition query_forward_entail_wit_3_1_split_goal_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) < target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (query_forward_search_inv map_l map_size_pre target_pre (mid + 1 ) high )
.

Definition query_forward_entail_wit_3_2 := 
(
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) >= target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((Zlength (map_l)) = map_size_pre) ” 
  &&  “ (0 <= map_size_pre) ” 
  &&  “ (map_size_pre <= 50000) ” 
  &&  “ (strict_increasing map_l ) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= ((mid - 1 ) + 1 )) ” 
  &&  “ ((mid - 1 ) < map_size_pre) ” 
  &&  “ (query_forward_search_inv map_l map_size_pre target_pre low (mid - 1 ) ) ”
  &&  (IntArray.full map_pre map_size_pre map_l )
) \/
(
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) >= target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  TT && emp 
|--
  “ (query_forward_search_inv map_l map_size_pre target_pre low (mid - 1 ) ) ”
  &&  emp
).

Definition query_forward_entail_wit_3_2_split_goal_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) >= target_pre)) (PreH2 : ((Znth mid map_l 0) <> target_pre)) (PreH3 : ((Zlength (map_l)) = map_size_pre)) (PreH4 : (0 <= map_size_pre)) (PreH5 : (map_size_pre <= 50000)) (PreH6 : (strict_increasing map_l )) (PreH7 : (0 <= low)) (PreH8 : (low <= mid)) (PreH9 : (mid <= high)) (PreH10 : (high < map_size_pre)) (PreH11 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (query_forward_search_inv map_l map_size_pre target_pre low (mid - 1 ) )
.

Definition query_forward_entail_wit_4 := 
(
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low > high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((Zlength (map_l)) = map_size_pre) ” 
  &&  “ (0 <= map_size_pre) ” 
  &&  “ (map_size_pre <= 50000) ” 
  &&  “ (strict_increasing map_l ) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= (high + 1 )) ” 
  &&  “ (high < map_size_pre) ” 
  &&  “ (query_forward_search_inv map_l map_size_pre target_pre low high ) ” 
  &&  “ (query_forward_result map_l map_size_pre target_pre (-1) ) ”
  &&  (IntArray.full map_pre map_size_pre map_l )
) \/
(
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low > high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  TT && emp 
|--
  “ (query_forward_result map_l map_size_pre target_pre (-1) ) ”
  &&  emp
).

Definition query_forward_entail_wit_4_split_goal_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (high: Z) (low: Z) (PreH1 : (low > high)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= (high + 1 ))) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (query_forward_result map_l map_size_pre target_pre (-1) )
.

Definition query_forward_return_wit_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (high: Z) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) (PreH5 : (0 <= low)) (PreH6 : (low <= (high + 1 ))) (PreH7 : (high < map_size_pre)) (PreH8 : (query_forward_search_inv map_l map_size_pre target_pre low high )) (PreH9 : (query_forward_result map_l map_size_pre target_pre (-1) )) ,
  (IntArray.full map_pre map_size_pre map_l )
|--
  “ (query_forward_result map_l map_size_pre target_pre (-1) ) ”
  &&  (IntArray.full map_pre map_size_pre map_l )
.

Definition query_forward_return_wit_2 := 
(
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) = target_pre)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= mid)) (PreH8 : (mid <= high)) (PreH9 : (high < map_size_pre)) (PreH10 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
|--
  “ (query_forward_result map_l map_size_pre target_pre mid ) ”
  &&  (IntArray.full map_pre map_size_pre map_l )
) \/
(
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) = target_pre)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= mid)) (PreH8 : (mid <= high)) (PreH9 : (high < map_size_pre)) (PreH10 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  TT && emp 
|--
  “ (query_forward_result map_l map_size_pre target_pre mid ) ”
  &&  emp
).

Definition query_forward_return_wit_2_split_goal_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) = target_pre)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= mid)) (PreH8 : (mid <= high)) (PreH9 : (high < map_size_pre)) (PreH10 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (query_forward_result map_l map_size_pre target_pre mid )
.

Definition query_forward_partial_solve_wit_1 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Zlength (map_l)) = map_size_pre)) (PreH2 : (0 <= map_size_pre)) (PreH3 : (map_size_pre <= 50000)) (PreH4 : (strict_increasing map_l )) (PreH5 : (0 <= low)) (PreH6 : (low <= mid)) (PreH7 : (mid <= high)) (PreH8 : (high < map_size_pre)) (PreH9 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((Zlength (map_l)) = map_size_pre) ” 
  &&  “ (0 <= map_size_pre) ” 
  &&  “ (map_size_pre <= 50000) ” 
  &&  “ (strict_increasing map_l ) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= mid) ” 
  &&  “ (mid <= high) ” 
  &&  “ (high < map_size_pre) ” 
  &&  “ (query_forward_search_inv map_l map_size_pre target_pre low high ) ”
  &&  (((map_pre + (mid * sizeof(INT)))) # Int  |-> (Znth mid map_l 0))
  **  (IntArray.missing_i map_pre mid 0 map_size_pre map_l )
.

Definition query_forward_partial_solve_wit_2 := 
forall (target_pre: Z) (map_size_pre: Z) (map_pre: Z) (map_l: (@list Z)) (low: Z) (mid: Z) (high: Z) (PreH1 : ((Znth mid map_l 0) <> target_pre)) (PreH2 : ((Zlength (map_l)) = map_size_pre)) (PreH3 : (0 <= map_size_pre)) (PreH4 : (map_size_pre <= 50000)) (PreH5 : (strict_increasing map_l )) (PreH6 : (0 <= low)) (PreH7 : (low <= mid)) (PreH8 : (mid <= high)) (PreH9 : (high < map_size_pre)) (PreH10 : (query_forward_search_inv map_l map_size_pre target_pre low high )) ,
  (IntArray.full map_pre map_size_pre map_l )
|--
  “ ((Znth mid map_l 0) <> target_pre) ” 
  &&  “ ((Zlength (map_l)) = map_size_pre) ” 
  &&  “ (0 <= map_size_pre) ” 
  &&  “ (map_size_pre <= 50000) ” 
  &&  “ (strict_increasing map_l ) ” 
  &&  “ (0 <= low) ” 
  &&  “ (low <= mid) ” 
  &&  “ (mid <= high) ” 
  &&  “ (high < map_size_pre) ” 
  &&  “ (query_forward_search_inv map_l map_size_pre target_pre low high ) ”
  &&  (((map_pre + (mid * sizeof(INT)))) # Int  |-> (Znth mid map_l 0))
  **  (IntArray.missing_i map_pre mid 0 map_size_pre map_l )
.

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
Axiom proof_of_int_array_quicksort_safety_wit_1 : int_array_quicksort_safety_wit_1.
Axiom proof_of_int_array_quicksort_safety_wit_2 : int_array_quicksort_safety_wit_2.
Axiom proof_of_int_array_quicksort_safety_wit_3 : int_array_quicksort_safety_wit_3.
Axiom proof_of_int_array_quicksort_return_wit_1 : int_array_quicksort_return_wit_1.
Axiom proof_of_int_array_quicksort_partial_solve_wit_1_pure : int_array_quicksort_partial_solve_wit_1_pure.
Axiom proof_of_int_array_quicksort_partial_solve_wit_1 : int_array_quicksort_partial_solve_wit_1.
Axiom proof_of_discretize_safety_wit_1 : discretize_safety_wit_1.
Axiom proof_of_discretize_safety_wit_2 : discretize_safety_wit_2.
Axiom proof_of_discretize_safety_wit_3 : discretize_safety_wit_3.
Axiom proof_of_discretize_safety_wit_4 : discretize_safety_wit_4.
Axiom proof_of_discretize_safety_wit_5 : discretize_safety_wit_5.
Axiom proof_of_discretize_safety_wit_6 : discretize_safety_wit_6.
Axiom proof_of_discretize_safety_wit_7 : discretize_safety_wit_7.
Axiom proof_of_discretize_safety_wit_8 : discretize_safety_wit_8.
Axiom proof_of_discretize_safety_wit_9 : discretize_safety_wit_9.
Axiom proof_of_discretize_entail_wit_1 : discretize_entail_wit_1.
Axiom proof_of_discretize_entail_wit_2 : discretize_entail_wit_2.
Axiom proof_of_discretize_entail_wit_3 : discretize_entail_wit_3.
Axiom proof_of_discretize_entail_wit_4 : discretize_entail_wit_4.
Axiom proof_of_discretize_entail_wit_5_1 : discretize_entail_wit_5_1.
Axiom proof_of_discretize_entail_wit_5_2 : discretize_entail_wit_5_2.
Axiom proof_of_discretize_entail_wit_6 : discretize_entail_wit_6.
Axiom proof_of_discretize_return_wit_1 : discretize_return_wit_1.
Axiom proof_of_discretize_partial_solve_wit_1 : discretize_partial_solve_wit_1.
Axiom proof_of_discretize_partial_solve_wit_2 : discretize_partial_solve_wit_2.
Axiom proof_of_discretize_partial_solve_wit_3_pure : discretize_partial_solve_wit_3_pure.
Axiom proof_of_discretize_partial_solve_wit_3 : discretize_partial_solve_wit_3.
Axiom proof_of_discretize_partial_solve_wit_4 : discretize_partial_solve_wit_4.
Axiom proof_of_discretize_partial_solve_wit_5 : discretize_partial_solve_wit_5.
Axiom proof_of_discretize_partial_solve_wit_6 : discretize_partial_solve_wit_6.
Axiom proof_of_discretize_partial_solve_wit_7 : discretize_partial_solve_wit_7.
Axiom proof_of_query_forward_safety_wit_1 : query_forward_safety_wit_1.
Axiom proof_of_query_forward_safety_wit_2 : query_forward_safety_wit_2.
Axiom proof_of_query_forward_safety_wit_3 : query_forward_safety_wit_3.
Axiom proof_of_query_forward_safety_wit_4 : query_forward_safety_wit_4.
Axiom proof_of_query_forward_safety_wit_5 : query_forward_safety_wit_5.
Axiom proof_of_query_forward_safety_wit_6 : query_forward_safety_wit_6.
Axiom proof_of_query_forward_safety_wit_7 : query_forward_safety_wit_7.
Axiom proof_of_query_forward_safety_wit_8 : query_forward_safety_wit_8.
Axiom proof_of_query_forward_safety_wit_9 : query_forward_safety_wit_9.
Axiom proof_of_query_forward_safety_wit_10 : query_forward_safety_wit_10.
Axiom proof_of_query_forward_safety_wit_11 : query_forward_safety_wit_11.
Axiom proof_of_query_forward_safety_wit_12 : query_forward_safety_wit_12.
Axiom proof_of_query_forward_safety_wit_13 : query_forward_safety_wit_13.
Axiom proof_of_query_forward_entail_wit_1 : query_forward_entail_wit_1.
Axiom proof_of_query_forward_entail_wit_2 : query_forward_entail_wit_2.
Axiom proof_of_query_forward_entail_wit_3_1 : query_forward_entail_wit_3_1.
Axiom proof_of_query_forward_entail_wit_3_2 : query_forward_entail_wit_3_2.
Axiom proof_of_query_forward_entail_wit_4 : query_forward_entail_wit_4.
Axiom proof_of_query_forward_return_wit_1 : query_forward_return_wit_1.
Axiom proof_of_query_forward_return_wit_2 : query_forward_return_wit_2.
Axiom proof_of_query_forward_partial_solve_wit_1 : query_forward_partial_solve_wit_1.
Axiom proof_of_query_forward_partial_solve_wit_2 : query_forward_partial_solve_wit_2.

End VC_Correct.
