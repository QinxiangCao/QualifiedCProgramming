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
Require Import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.

(*----- Function quicksort_numbers -----*)

Definition quicksort_numbers_safety_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= low_pre)) (PreH6 : (low_pre <= count_pre)) (PreH7 : ((-1) <= high_pre)) (PreH8 : (high_pre < count_pre)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : ((Zlength (rows)) = count_pre)) (PreH12 : ((Zlength (lens)) = count_pre)) (PreH13 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH14 : (Forall (Z.le (1)) lens )) (PreH15 : (Forall (Z.ge (number_width_pre)) lens )) (PreH16 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH17 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH18 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH19 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_numbers_safety_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (0 > low_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= low_pre)) (PreH7 : (low_pre <= count_pre)) (PreH8 : ((-1) <= high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : ((Zlength (rows)) = count_pre)) (PreH13 : ((Zlength (lens)) = count_pre)) (PreH14 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH15 : (Forall (Z.le (1)) lens )) (PreH16 : (Forall (Z.ge (number_width_pre)) lens )) (PreH17 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH18 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH19 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH20 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH21 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
|--
  “ False ”
.

Definition quicksort_numbers_safety_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (high_pre >= count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH17 : (Forall (Z.le (1)) lens )) (PreH18 : (Forall (Z.ge (number_width_pre)) lens )) (PreH19 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH20 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH21 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH22 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
|--
  “ False ”
.

Definition quicksort_numbers_safety_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH17 : (Forall (Z.le (1)) lens )) (PreH18 : (Forall (Z.ge (number_width_pre)) lens )) (PreH19 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH20 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH21 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH22 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "boundary" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "pivot_length" ) )) # Int  |-> (Znth high_pre lens 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
|--
  “ ((low_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (low_pre - 1 )) ”
.

Definition quicksort_numbers_safety_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH17 : (Forall (Z.le (1)) lens )) (PreH18 : (Forall (Z.ge (number_width_pre)) lens )) (PreH19 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH20 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH21 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH22 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "boundary" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "pivot_length" ) )) # Int  |-> (Znth high_pre lens 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_numbers_safety_wit_6 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan < high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "total_length" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |-> (Znth scan lens1 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((Znth scan lens1 0) + pivot_length ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth scan lens1 0) + pivot_length )) ”
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan < high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "total_length" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |-> (Znth scan lens1 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((Znth scan lens1 0) + pivot_length ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth scan lens1 0) + pivot_length )) ”
).

Definition quicksort_numbers_safety_wit_6_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan < high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "total_length" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |-> (Znth scan lens1 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((Znth scan lens1 0) + pivot_length ) <= INT_MAX) ”
.

Definition quicksort_numbers_safety_wit_6_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan < high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "total_length" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |-> (Znth scan lens1 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((INT_MIN) <= ((Znth scan lens1 0) + pivot_length )) ”
.

Definition quicksort_numbers_safety_wit_7 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan < high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "comparison" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |-> ((Znth scan lens1 0) + pivot_length ))
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |-> (Znth scan lens1 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_numbers_safety_wit_8 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan < high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "comparison" ) )) # Int  |-> 0)
  **  ((( &( "total_length" ) )) # Int  |-> ((Znth scan lens1 0) + pivot_length ))
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |-> (Znth scan lens1 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_numbers_safety_wit_9 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "left_digit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((scan * number_width_pre ) + position ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((scan * number_width_pre ) + position )) ”
.

Definition quicksort_numbers_safety_wit_10 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "left_digit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((scan * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_11 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "left_digit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((high_pre * number_width_pre ) + (position - current_length ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((high_pre * number_width_pre ) + (position - current_length ) )) ”
.

Definition quicksort_numbers_safety_wit_12 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "left_digit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((position - current_length ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (position - current_length )) ”
.

Definition quicksort_numbers_safety_wit_13 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "left_digit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((high_pre * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (high_pre * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_14 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position < pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_digit" ) )) # Int  |-> left_digit)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((high_pre * number_width_pre ) + position ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((high_pre * number_width_pre ) + position )) ”
.

Definition quicksort_numbers_safety_wit_15 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position < pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_digit" ) )) # Int  |-> left_digit)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((high_pre * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (high_pre * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_16 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position >= pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_digit" ) )) # Int  |-> left_digit)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((scan * number_width_pre ) + (position - pivot_length ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((scan * number_width_pre ) + (position - pivot_length ) )) ”
.

Definition quicksort_numbers_safety_wit_17 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position >= pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_digit" ) )) # Int  |-> left_digit)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((position - pivot_length ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (position - pivot_length )) ”
.

Definition quicksort_numbers_safety_wit_18 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position >= pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_digit" ) )) # Int  |-> left_digit)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "right_digit" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((scan * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_19 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (right_digit: Z) (PreH1 : (left_digit <> right_digit)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH34 : (Forall (Z.le (1)) lens1 )) (PreH35 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH36 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_digit" ) )) # Int  |-> left_digit)
  **  ((( &( "right_digit" ) )) # Int  |-> right_digit)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((left_digit - right_digit ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_digit - right_digit )) ”
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (right_digit: Z) (PreH1 : (left_digit <> right_digit)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH34 : (Forall (Z.le (1)) lens1 )) (PreH35 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH36 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_digit" ) )) # Int  |-> left_digit)
  **  ((( &( "right_digit" ) )) # Int  |-> right_digit)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((left_digit - right_digit ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_digit - right_digit )) ”
).

Definition quicksort_numbers_safety_wit_19_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (right_digit: Z) (PreH1 : (left_digit <> right_digit)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH34 : (Forall (Z.le (1)) lens1 )) (PreH35 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH36 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_digit" ) )) # Int  |-> left_digit)
  **  ((( &( "right_digit" ) )) # Int  |-> right_digit)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((left_digit - right_digit ) <= INT_MAX) ”
.

Definition quicksort_numbers_safety_wit_19_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (right_digit: Z) (PreH1 : (left_digit <> right_digit)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH34 : (Forall (Z.le (1)) lens1 )) (PreH35 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH36 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_digit" ) )) # Int  |-> left_digit)
  **  ((( &( "right_digit" ) )) # Int  |-> right_digit)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((INT_MIN) <= (left_digit - right_digit )) ”
.

Definition quicksort_numbers_safety_wit_20 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (right_digit: Z) (PreH1 : (left_digit = right_digit)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1)) = count_pre)) (PreH32 : ((Zlength (lens1)) = count_pre)) (PreH33 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH34 : (Forall (Z.le (1)) lens1 )) (PreH35 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH36 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH41 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH42 : ((sum (lens1)) = (sum (lens)))) (PreH43 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((position + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (position + 1 )) ”
.

Definition quicksort_numbers_safety_wit_21 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (PreH1 : (0 <= (scan * number_width_pre ))) (PreH2 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH3 : (0 <= (high_pre * number_width_pre ))) (PreH4 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (0 <= low_pre)) (PreH10 : (low_pre < high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : ((low_pre - 1 ) <= boundary)) (PreH13 : (boundary < scan)) (PreH14 : (low_pre <= scan)) (PreH15 : (scan < high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH19 : (current_length = (Znth (scan) (lens1) (0)))) (PreH20 : (1 <= current_length)) (PreH21 : (current_length <= number_width_pre)) (PreH22 : (1 <= pivot_length)) (PreH23 : (pivot_length <= number_width_pre)) (PreH24 : (total_length = (current_length + pivot_length ))) (PreH25 : ((Zlength (rows1)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH34 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH35 : (ConcatCompareOutcome rows1 lens1 scan high_pre comparison )) (PreH36 : ((sum (lens1)) = (sum (lens)))) (PreH37 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_numbers_safety_wit_22 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (PreH1 : (comparison > 0)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : ((Zlength (rows1)) = count_pre)) (PreH27 : ((Zlength (lens1)) = count_pre)) (PreH28 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH29 : (Forall (Z.le (1)) lens1 )) (PreH30 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH31 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH32 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH33 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH34 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH35 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH36 : (ConcatCompareOutcome rows1 lens1 scan high_pre comparison )) (PreH37 : ((sum (lens1)) = (sum (lens)))) (PreH38 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "column" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((boundary + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (boundary + 1 )) ”
.

Definition quicksort_numbers_safety_wit_23 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (PreH1 : (comparison > 0)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : ((Zlength (rows1)) = count_pre)) (PreH27 : ((Zlength (lens1)) = count_pre)) (PreH28 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH29 : (Forall (Z.le (1)) lens1 )) (PreH30 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH31 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH32 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH33 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH34 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH35 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH36 : (ConcatCompareOutcome rows1 lens1 scan high_pre comparison )) (PreH37 : ((sum (lens1)) = (sum (lens)))) (PreH38 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "column" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "boundary" ) )) # Int  |-> (boundary + 1 ))
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_numbers_safety_wit_24 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  ((( &( "temporary_digit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((boundary * number_width_pre ) + column ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((boundary * number_width_pre ) + column )) ”
.

Definition quicksort_numbers_safety_wit_25 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  ((( &( "temporary_digit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((boundary * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (boundary * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_26 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((boundary * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((boundary * number_width_pre ) + column ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((boundary * number_width_pre ) + column )) ”
.

Definition quicksort_numbers_safety_wit_27 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((boundary * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((boundary * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (boundary * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_28 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((boundary * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((scan * number_width_pre ) + column ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((scan * number_width_pre ) + column )) ”
.

Definition quicksort_numbers_safety_wit_29 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((boundary * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((scan * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_30 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((boundary * number_width_pre ) + column )) ((Znth ((scan * number_width_pre ) + column ) flat_now 0)) (flat_now)) )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((boundary * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (((scan * number_width_pre ) + column ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((scan * number_width_pre ) + column )) ”
.

Definition quicksort_numbers_safety_wit_31 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((boundary * number_width_pre ) + column )) ((Znth ((scan * number_width_pre ) + column ) flat_now 0)) (flat_now)) )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((boundary * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((scan * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_32 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((scan * number_width_pre ) + column )) ((Znth ((boundary * number_width_pre ) + column ) flat_now 0)) ((replace_Znth (((boundary * number_width_pre ) + column )) ((Znth ((scan * number_width_pre ) + column ) flat_now 0)) (flat_now)))) )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "temporary_length" ) )) # Int  |->_)
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((column + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (column + 1 )) ”
.

Definition quicksort_numbers_safety_wit_33 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (boundary: Z) (scan: Z) (pivot_length: Z) (PreH1 : (0 <= (high_pre * number_width_pre ))) (PreH2 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : ((low_pre - 1 ) <= boundary)) (PreH11 : (boundary <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH21 : (Forall (Z.le (1)) lens1 )) (PreH22 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH23 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH25 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH27 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1 ) )) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((scan + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (scan + 1 )) ”
.

Definition quicksort_numbers_safety_wit_34 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan >= high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ ((boundary + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (boundary + 1 )) ”
.

Definition quicksort_numbers_safety_wit_35 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan >= high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_numbers_safety_wit_36 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan >= high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "column" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot" ) )) # Int  |-> (boundary + 1 ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition quicksort_numbers_safety_wit_37 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  ((( &( "temporary_digit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
|--
  “ (((pivot * number_width_pre ) + column ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((pivot * number_width_pre ) + column )) ”
.

Definition quicksort_numbers_safety_wit_38 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  ((( &( "temporary_digit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
|--
  “ ((pivot * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_39 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((pivot * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
|--
  “ (((pivot * number_width_pre ) + column ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((pivot * number_width_pre ) + column )) ”
.

Definition quicksort_numbers_safety_wit_40 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((pivot * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
|--
  “ ((pivot * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_41 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((pivot * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
|--
  “ (((high_pre * number_width_pre ) + column ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((high_pre * number_width_pre ) + column )) ”
.

Definition quicksort_numbers_safety_wit_42 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((pivot * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
|--
  “ ((high_pre * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (high_pre * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_43 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((pivot * number_width_pre ) + column )) ((Znth ((high_pre * number_width_pre ) + column ) flat_now 0)) (flat_now)) )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((pivot * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
|--
  “ (((high_pre * number_width_pre ) + column ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((high_pre * number_width_pre ) + column )) ”
.

Definition quicksort_numbers_safety_wit_44 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((pivot * number_width_pre ) + column )) ((Znth ((high_pre * number_width_pre ) + column ) flat_now 0)) (flat_now)) )
  **  ((( &( "temporary_digit" ) )) # Int  |-> (Znth ((pivot * number_width_pre ) + column ) flat_now 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
|--
  “ ((high_pre * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (high_pre * number_width_pre )) ”
.

Definition quicksort_numbers_safety_wit_45 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((high_pre * number_width_pre ) + column )) ((Znth ((pivot * number_width_pre ) + column ) flat_now 0)) ((replace_Znth (((pivot * number_width_pre ) + column )) ((Znth ((high_pre * number_width_pre ) + column ) flat_now 0)) (flat_now)))) )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "column" ) )) # Int  |-> column)
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
|--
  “ ((column + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (column + 1 )) ”
.

Definition quicksort_numbers_safety_wit_46 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (PreH1 : (pivot > low_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH28 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ ((pivot - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot - 1 )) ”
.

Definition quicksort_numbers_safety_wit_47 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (PreH1 : (pivot > low_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH28 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_numbers_safety_wit_48 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot < high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH3 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH4 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH6 : (pivot > low_pre)) (PreH7 : (0 <= (pivot * number_width_pre ))) (PreH8 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH9 : (0 <= (high_pre * number_width_pre ))) (PreH10 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : (0 <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH31 : (PairedPermutation rows rows1 lens lens1 )) (PreH32 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH33 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH34 : ((sum (lens1)) = (sum (lens)))) (PreH35 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ ((pivot + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot + 1 )) ”
.

Definition quicksort_numbers_safety_wit_49 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot < high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH3 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH4 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH6 : (pivot > low_pre)) (PreH7 : (0 <= (pivot * number_width_pre ))) (PreH8 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH9 : (0 <= (high_pre * number_width_pre ))) (PreH10 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : (0 <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH31 : (PairedPermutation rows rows1 lens lens1 )) (PreH32 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH33 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH34 : ((sum (lens1)) = (sum (lens)))) (PreH35 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_numbers_safety_wit_50 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (PreH1 : (pivot >= high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (0 <= (pivot * number_width_pre ))) (PreH4 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH21 : (Forall (Z.le (1)) lens1 )) (PreH22 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH23 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH25 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH27 : (PairedPermutation rows rows1 lens lens1 )) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ False ”
.

Definition quicksort_numbers_safety_wit_51 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (0 <= (pivot * number_width_pre ))) (PreH4 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH21 : (Forall (Z.le (1)) lens1 )) (PreH22 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH23 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH25 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH27 : (PairedPermutation rows rows1 lens lens1 )) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ ((pivot + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pivot + 1 )) ”
.

Definition quicksort_numbers_safety_wit_52 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (0 <= (pivot * number_width_pre ))) (PreH4 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH21 : (Forall (Z.le (1)) lens1 )) (PreH22 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH23 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH25 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH27 : (PairedPermutation rows rows1 lens lens1 )) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition quicksort_numbers_entail_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH17 : (Forall (Z.le (1)) lens )) (PreH18 : (Forall (Z.ge (number_width_pre)) lens )) (PreH19 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH20 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH21 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH22 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
|--
  EX (flat1: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= (low_pre - 1 )) ” 
  &&  “ ((low_pre - 1 ) < low_pre) ” 
  &&  “ (low_pre <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Znth high_pre lens 0) = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= (Znth high_pre lens 0)) ” 
  &&  “ ((Znth high_pre lens 0) <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre (low_pre - 1 ) low_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH17 : (Forall (Z.le (1)) lens )) (PreH18 : (Forall (Z.ge (number_width_pre)) lens )) (PreH19 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH20 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH21 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH22 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= ((Zlength (rows)) * number_width_pre )) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (high_pre < (Zlength (rows))) ” 
  &&  “ ((low_pre - 1 ) <= (low_pre - 1 )) ” 
  &&  “ ((low_pre - 1 ) < low_pre) ” 
  &&  “ (low_pre <= low_pre) ” 
  &&  “ (low_pre <= high_pre) ” 
  &&  “ ((Znth high_pre lens 0) = (Znth (high_pre) (lens) (0))) ” 
  &&  “ (1 <= (Znth high_pre lens 0)) ” 
  &&  “ ((Znth high_pre lens 0) <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens low_pre high_pre (low_pre - 1 ) low_pre ) ” 
  &&  “ (FlatRows flat rows1 (Zlength (rows)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_2 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (rows1_2: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan < high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1_2)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1)) )) (PreH29 : (PartitionScanState rows rows1_2 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
|--
  EX (flat1: (@list Z))  (rows1: (@list (@list Z)))  (lens1_2: (@list Z)) ,
  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1_2) (0))) ” 
  &&  “ ((Znth scan lens1 0) = (Znth (scan) (lens1_2) (0))) ” 
  &&  “ (1 <= (Znth scan lens1 0)) ” 
  &&  “ ((Znth scan lens1 0) <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (((Znth scan lens1 0) + pivot_length ) = ((Znth scan lens1 0) + pivot_length )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((Znth scan lens1 0) + pivot_length )) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1_2)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1_2 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1_2 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre 0 ) ” 
  &&  “ ((sum (lens1_2)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (rows1_2: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan < high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1_2)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1)) )) (PreH29 : (PartitionScanState rows rows1_2 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= ((Zlength (rows1_2)) * number_width_pre )) ” 
  &&  “ ((Znth scan lens1 0) = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= (Znth scan lens1 0)) ” 
  &&  “ ((Znth scan lens1 0) <= number_width_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((Znth scan lens1 0) + (Znth (high_pre) (lens1) (0)) )) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre 0 ) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_3_1 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1_2: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1_2: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH33 : (Forall (Z.le (1)) lens1_2 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1_2: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ (comparison = 0) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ ((Znth ((scan * number_width_pre ) + position ) flat1 0) = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre position ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1_2 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1_2: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1_2: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH33 : (Forall (Z.le (1)) lens1_2 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((Znth ((scan * number_width_pre ) + position ) flat1 0) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position ) ” 
  &&  “ (FlatRows flat1 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_3_2 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1_2: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1_2: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH33 : (Forall (Z.le (1)) lens1_2 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1_2: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ (comparison = 0) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ ((Znth ((high_pre * number_width_pre ) + (position - current_length ) ) flat1 0) = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre position ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1_2 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1_2: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1_2: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH33 : (Forall (Z.le (1)) lens1_2 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((Znth ((high_pre * number_width_pre ) + (position - (Znth (scan) (lens1_2) (0)) ) ) flat1 0) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position ) ” 
  &&  “ (FlatRows flat1 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_4_1 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position < pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH33 : (Forall (Z.le (1)) lens1_2 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1_2: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ (comparison = 0) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” 
  &&  “ ((Znth ((high_pre * number_width_pre ) + position ) flat1 0) = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre position ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1_2 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position < pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH33 : (Forall (Z.le (1)) lens1_2 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” 
  &&  “ ((Znth ((high_pre * number_width_pre ) + position ) flat1 0) = (ConcatRightDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position ) ” 
  &&  “ (FlatRows flat1 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_4_2 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position >= pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH33 : (Forall (Z.le (1)) lens1_2 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1_2: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ (comparison = 0) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” 
  &&  “ ((Znth ((scan * number_width_pre ) + (position - pivot_length ) ) flat1 0) = (ConcatRightDigit (rows1) (lens1) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre position ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1_2 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position >= pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1_2)) = count_pre)) (PreH31 : ((Zlength (lens1_2)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH33 : (Forall (Z.le (1)) lens1_2 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH41 : ((sum (lens1_2)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) = (ConcatLeftDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” 
  &&  “ ((Znth ((scan * number_width_pre ) + (position - (Znth (high_pre) (lens1_2) (0)) ) ) flat1 0) = (ConcatRightDigit (rows1) (lens1_2) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre position ) ” 
  &&  “ (FlatRows flat1 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_5 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (right_digit: Z) (PreH1 : (left_digit = right_digit)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1_2)) = count_pre)) (PreH32 : ((Zlength (lens1_2)) = count_pre)) (PreH33 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH34 : (Forall (Z.le (1)) lens1_2 )) (PreH35 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH36 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH38 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH40 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH41 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH42 : ((sum (lens1_2)) = (sum (lens)))) (PreH43 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ (comparison = 0) ” 
  &&  “ (0 <= (position + 1 )) ” 
  &&  “ ((position + 1 ) <= total_length) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre (position + 1 ) ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (right_digit: Z) (PreH1 : (left_digit = right_digit)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1_2)) = count_pre)) (PreH32 : ((Zlength (lens1_2)) = count_pre)) (PreH33 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH34 : (Forall (Z.le (1)) lens1_2 )) (PreH35 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH36 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH38 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH40 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH41 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH42 : ((sum (lens1_2)) = (sum (lens)))) (PreH43 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (0 <= (position + 1 )) ” 
  &&  “ ((position + 1 ) <= (current_length + pivot_length )) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1_2 scan high_pre (position + 1 ) ) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_6_1 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (rows1_2: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1_2: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position >= total_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position <= total_length)) (PreH29 : ((Zlength (rows1_2)) = count_pre)) (PreH30 : ((Zlength (lens1_2)) = count_pre)) (PreH31 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH32 : (Forall (Z.le (1)) lens1_2 )) (PreH33 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH34 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH35 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH37 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH39 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH40 : ((sum (lens1_2)) = (sum (lens)))) (PreH41 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatCompareOutcome rows1 lens1 scan high_pre comparison ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "position" ) )) # Int  |->_)
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (rows1_2: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1_2: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position >= total_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position <= total_length)) (PreH29 : ((Zlength (rows1_2)) = count_pre)) (PreH30 : ((Zlength (lens1_2)) = count_pre)) (PreH31 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH32 : (Forall (Z.le (1)) lens1_2 )) (PreH33 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH34 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH35 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH36 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH37 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH38 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH39 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH40 : ((sum (lens1_2)) = (sum (lens)))) (PreH41 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatCompareOutcome rows1 lens1_2 scan high_pre 0 ) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_6_2 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (right_digit: Z) (PreH1 : (left_digit <> right_digit)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1_2)) = count_pre)) (PreH32 : ((Zlength (lens1_2)) = count_pre)) (PreH33 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH34 : (Forall (Z.le (1)) lens1_2 )) (PreH35 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH36 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH38 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH40 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH41 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH42 : ((sum (lens1_2)) = (sum (lens)))) (PreH43 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatCompareOutcome rows1 lens1 scan high_pre (left_digit - right_digit ) ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "position" ) )) # Int  |->_)
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (right_digit: Z) (PreH1 : (left_digit <> right_digit)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH30 : (right_digit = (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)))) (PreH31 : ((Zlength (rows1_2)) = count_pre)) (PreH32 : ((Zlength (lens1_2)) = count_pre)) (PreH33 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH34 : (Forall (Z.le (1)) lens1_2 )) (PreH35 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH36 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH37 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH38 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH39 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH40 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH41 : (ConcatComparePrefix rows1_2 lens1_2 scan high_pre position )) (PreH42 : ((sum (lens1_2)) = (sum (lens)))) (PreH43 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatCompareOutcome rows1 lens1_2 scan high_pre ((ConcatLeftDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) - (ConcatRightDigit (rows1_2) (lens1_2) (scan) (high_pre) (position)) ) ) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_7 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1_2: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (PreH1 : (comparison > 0)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : ((Zlength (rows1)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH29 : (Forall (Z.le (1)) lens1_2 )) (PreH30 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH31 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH32 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH33 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) )) (PreH34 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) )) (PreH35 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan )) (PreH36 : (ConcatCompareOutcome rows1 lens1_2 scan high_pre comparison )) (PreH37 : ((sum (lens1_2)) = (sum (lens)))) (PreH38 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat_now: (@list Z))  (rows_now: (@list (@list Z)))  (rows_before: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= ((boundary + 1 ) * number_width_pre )) ” 
  &&  “ ((((boundary + 1 ) * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= (boundary + 1 )) ” 
  &&  “ ((boundary + 1 ) <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre ((boundary + 1 ) - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now (boundary + 1 ) scan 0 number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1_2: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (PreH1 : (comparison > 0)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : ((Zlength (rows1)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH29 : (Forall (Z.le (1)) lens1_2 )) (PreH30 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH31 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH32 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH33 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) )) (PreH34 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) )) (PreH35 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan )) (PreH36 : (ConcatCompareOutcome rows1 lens1_2 scan high_pre comparison )) (PreH37 : ((sum (lens1_2)) = (sum (lens)))) (PreH38 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows_now: (@list (@list Z)))  (rows_before: (@list (@list Z))) ,
  “ (0 <= ((boundary + 1 ) * number_width_pre )) ” 
  &&  “ ((((boundary + 1 ) * number_width_pre ) + number_width_pre ) <= ((Zlength (rows1)) * number_width_pre )) ” 
  &&  “ (low_pre <= (boundary + 1 )) ” 
  &&  “ ((boundary + 1 ) <= scan) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = (Zlength (rows1))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre ((boundary + 1 ) - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now (boundary + 1 ) scan 0 number_width_pre ) ” 
  &&  “ (FlatRows flat1 rows_now (Zlength (rows1)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_8 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now_2: (@list Z)) (rows_now_2: (@list (@list Z))) (comparison: Z) (rows_before_2: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before_2)) = count_pre)) (PreH26 : ((Zlength (lens1_2)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before_2)) )) (PreH28 : (Forall (Z.le (1)) lens1_2 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before_2)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before_2)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before_2) (lens1_2)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before_2) (lens1_2)) )) (PreH34 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before_2 lens1_2 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before_2 rows_now_2 boundary scan column number_width_pre )) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((scan * number_width_pre ) + column )) ((Znth ((boundary * number_width_pre ) + column ) flat_now_2 0)) ((replace_Znth (((boundary * number_width_pre ) + column )) ((Znth ((scan * number_width_pre ) + column ) flat_now_2 0)) (flat_now_2)))) )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat_now: (@list Z))  (rows_now: (@list (@list Z)))  (rows_before: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (boundary * number_width_pre )) ” 
  &&  “ (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= (column + 1 )) ” 
  &&  “ ((column + 1 ) <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan (column + 1 ) number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now_2: (@list Z)) (rows_now_2: (@list (@list Z))) (comparison: Z) (rows_before_2: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before_2)) = count_pre)) (PreH26 : ((Zlength (lens1_2)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before_2)) )) (PreH28 : (Forall (Z.le (1)) lens1_2 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before_2)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before_2)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before_2) (lens1_2)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before_2) (lens1_2)) )) (PreH34 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before_2 lens1_2 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before_2 rows_now_2 boundary scan column number_width_pre )) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows_now: (@list (@list Z)))  (rows_before: (@list (@list Z))) ,
  “ (0 <= (column + 1 )) ” 
  &&  “ ((column + 1 ) <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = (Zlength (rows_before_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan (column + 1 ) number_width_pre ) ” 
  &&  “ (FlatRows (replace_Znth (((scan * number_width_pre ) + column )) ((Znth ((boundary * number_width_pre ) + column ) flat_now_2 0)) ((replace_Znth (((boundary * number_width_pre ) + column )) ((Znth ((scan * number_width_pre ) + column ) flat_now_2 0)) (flat_now_2)))) rows_now (Zlength (rows_before_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_9_1 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1_2)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1_2 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1_2)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1_2)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre (replace_Znth (scan) ((Znth boundary lens1_2 0)) ((replace_Znth (boundary) ((Znth scan lens1_2 0)) (lens1_2)))) )
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
|--
  EX (flat1: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1 ) ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "comparison" ) )) # Int  |->_)
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1_2)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1_2 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1_2)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1_2)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1_2 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ ((Znth (high_pre) (lens1_2) (0)) = (Znth (high_pre) ((replace_Znth (scan) ((Znth boundary lens1_2 0)) ((replace_Znth (boundary) ((Znth scan lens1_2 0)) (lens1_2))))) (0))) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows_before))) ” 
  &&  “ ((Zlength ((replace_Znth (scan) ((Znth boundary lens1_2 0)) ((replace_Znth (boundary) ((Znth scan lens1_2 0)) (lens1_2)))))) = (Zlength (rows_before))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (replace_Znth (scan) ((Znth boundary lens1_2 0)) ((replace_Znth (boundary) ((Znth scan lens1_2 0)) (lens1_2)))) ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) (replace_Znth (scan) ((Znth boundary lens1_2 0)) ((replace_Znth (boundary) ((Znth scan lens1_2 0)) (lens1_2)))) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) ((replace_Znth (scan) ((Znth boundary lens1_2 0)) ((replace_Znth (boundary) ((Znth scan lens1_2 0)) (lens1_2)))))) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) ((replace_Znth (scan) ((Znth boundary lens1_2 0)) ((replace_Znth (boundary) ((Znth scan lens1_2 0)) (lens1_2)))))) ) ” 
  &&  “ (PartitionScanState rows rows1 lens (replace_Znth (scan) ((Znth boundary lens1_2 0)) ((replace_Znth (boundary) ((Znth scan lens1_2 0)) (lens1_2)))) low_pre high_pre boundary (scan + 1 ) ) ” 
  &&  “ ((sum ((replace_Znth (scan) ((Znth boundary lens1_2 0)) ((replace_Znth (boundary) ((Znth scan lens1_2 0)) (lens1_2)))))) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows1 (Zlength (rows_before)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_9_2 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (PreH1 : (comparison <= 0)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : ((Zlength (rows1_2)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH29 : (Forall (Z.le (1)) lens1_2 )) (PreH30 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH31 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH32 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH33 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH34 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH35 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH36 : (ConcatCompareOutcome rows1_2 lens1_2 scan high_pre comparison )) (PreH37 : ((sum (lens1_2)) = (sum (lens)))) (PreH38 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  ((( &( "current_length" ) )) # Int  |-> current_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "comparison" ) )) # Int  |-> comparison)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1 ) ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "current_length" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |->_)
  **  ((( &( "comparison" ) )) # Int  |->_)
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (PreH1 : (comparison <= 0)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1_2) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : ((Zlength (rows1_2)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH29 : (Forall (Z.le (1)) lens1_2 )) (PreH30 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH31 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH32 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH33 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH34 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH35 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary scan )) (PreH36 : (ConcatCompareOutcome rows1_2 lens1_2 scan high_pre comparison )) (PreH37 : ((sum (lens1_2)) = (sum (lens)))) (PreH38 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (boundary <= scan) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary (scan + 1 ) ) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_10 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (boundary: Z) (scan: Z) (pivot_length: Z) (PreH1 : (0 <= (high_pre * number_width_pre ))) (PreH2 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : ((low_pre - 1 ) <= boundary)) (PreH11 : (boundary <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : ((Zlength (rows1_2)) = count_pre)) (PreH19 : ((Zlength (lens1_2)) = count_pre)) (PreH20 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH21 : (Forall (Z.le (1)) lens1_2 )) (PreH22 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH23 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH24 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH25 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH26 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH27 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary (scan + 1 ) )) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < (scan + 1 )) ” 
  &&  “ (low_pre <= (scan + 1 )) ” 
  &&  “ ((scan + 1 ) <= high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary (scan + 1 ) ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (boundary: Z) (scan: Z) (pivot_length: Z) (PreH1 : (0 <= (high_pre * number_width_pre ))) (PreH2 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre < high_pre)) (PreH9 : (high_pre < count_pre)) (PreH10 : ((low_pre - 1 ) <= boundary)) (PreH11 : (boundary <= scan)) (PreH12 : (scan < high_pre)) (PreH13 : (1 <= (sum (lens)))) (PreH14 : ((sum (lens)) <= 200)) (PreH15 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH16 : (1 <= pivot_length)) (PreH17 : (pivot_length <= number_width_pre)) (PreH18 : ((Zlength (rows1_2)) = count_pre)) (PreH19 : ((Zlength (lens1_2)) = count_pre)) (PreH20 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH21 : (Forall (Z.le (1)) lens1_2 )) (PreH22 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH23 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH24 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH25 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH26 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH27 : (PartitionScanState rows rows1_2 lens lens1_2 low_pre high_pre boundary (scan + 1 ) )) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (boundary < (scan + 1 )) ” 
  &&  “ (low_pre <= (scan + 1 )) ” 
  &&  “ ((scan + 1 ) <= high_pre) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary (scan + 1 ) ) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_11 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan >= high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1_2)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1_2 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "boundary" ) )) # Int  |-> boundary)
  **  ((( &( "scan" ) )) # Int  |-> scan)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat_now: (@list Z))  (rows_now: (@list (@list Z)))  (rows_before: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= ((boundary + 1 ) * number_width_pre )) ” 
  &&  “ ((((boundary + 1 ) * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= (boundary + 1 )) ” 
  &&  “ ((boundary + 1 ) <= high_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre ((boundary + 1 ) - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now (boundary + 1 ) high_pre 0 number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan >= high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1_2)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1_2 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1_2 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1_2)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows_now: (@list (@list Z)))  (rows_before: (@list (@list Z))) ,
  “ (0 <= ((boundary + 1 ) * number_width_pre )) ” 
  &&  “ ((((boundary + 1 ) * number_width_pre ) + number_width_pre ) <= ((Zlength (rows1)) * number_width_pre )) ” 
  &&  “ (low_pre <= (boundary + 1 )) ” 
  &&  “ ((boundary + 1 ) <= high_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = (Zlength (rows1))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre ((boundary + 1 ) - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now (boundary + 1 ) high_pre 0 number_width_pre ) ” 
  &&  “ (FlatRows flat1 rows_now (Zlength (rows1)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_12 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now_2: (@list Z)) (rows_now_2: (@list (@list Z))) (rows_before_2: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before_2)) )) (PreH25 : (Forall (Z.le (1)) lens1_2 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before_2)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before_2)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before_2) (lens1_2)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before_2) (lens1_2)) )) (PreH31 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before_2 rows_now_2 pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((high_pre * number_width_pre ) + column )) ((Znth ((pivot * number_width_pre ) + column ) flat_now_2 0)) ((replace_Znth (((pivot * number_width_pre ) + column )) ((Znth ((high_pre * number_width_pre ) + column ) flat_now_2 0)) (flat_now_2)))) )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat_now: (@list Z))  (rows_now: (@list (@list Z)))  (rows_before: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (0 <= (column + 1 )) ” 
  &&  “ ((column + 1 ) <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now pivot high_pre (column + 1 ) number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now_2: (@list Z)) (rows_now_2: (@list (@list Z))) (rows_before_2: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before_2)) )) (PreH25 : (Forall (Z.le (1)) lens1_2 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before_2)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before_2)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before_2) (lens1_2)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before_2) (lens1_2)) )) (PreH31 : (PartitionScanState rows rows_before_2 lens lens1_2 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before_2 rows_now_2 pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now_2 rows_now_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows_now: (@list (@list Z)))  (rows_before: (@list (@list Z))) ,
  “ (0 <= (column + 1 )) ” 
  &&  “ ((column + 1 ) <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = (Zlength (rows_before_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1_2)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now pivot high_pre (column + 1 ) number_width_pre ) ” 
  &&  “ (FlatRows (replace_Znth (((high_pre * number_width_pre ) + column )) ((Znth ((pivot * number_width_pre ) + column ) flat_now_2 0)) ((replace_Znth (((pivot * number_width_pre ) + column )) ((Znth ((high_pre * number_width_pre ) + column ) flat_now_2 0)) (flat_now_2)))) rows_now (Zlength (rows_before_2)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_entail_wit_13 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1_2 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1_2)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1_2)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre (replace_Znth (pivot) (pivot_length) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))) )
  **  ((( &( "pivot_length" ) )) # Int  |-> pivot_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
|--
  EX (flat1: (@list Z))  (lens1: (@list Z))  (rows1: (@list (@list Z))) ,
  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre ) ” 
  &&  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "pivot_length" ) )) # Int  |->_)
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1_2: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1_2) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1_2 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1_2)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1_2)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1_2 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1_2)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((Zlength (rows1)) = (Zlength (rows_before))) ” 
  &&  “ ((Zlength ((replace_Znth (pivot) ((Znth (high_pre) (lens1_2) (0))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))))) = (Zlength (rows_before))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) (0))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))) ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) (0))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) ((replace_Znth (pivot) ((Znth (high_pre) (lens1_2) (0))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))))) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) ((replace_Znth (pivot) ((Znth (high_pre) (lens1_2) (0))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))))) ) ” 
  &&  “ (PairedPermutation rows rows1 lens (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) (0))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))) ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) (0))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))) low_pre high_pre ) ” 
  &&  “ (GreedyPartitionedAt rows1 (replace_Znth (pivot) ((Znth (high_pre) (lens1_2) (0))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))) low_pre high_pre pivot ) ” 
  &&  “ ((sum ((replace_Znth (pivot) ((Znth (high_pre) (lens1_2) (0))) ((replace_Znth (high_pre) ((Znth pivot lens1_2 0)) (lens1_2)))))) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows1 (Zlength (rows_before)) number_width_pre ) ”
  &&  emp
).

Definition quicksort_numbers_return_wit_1 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (lens1_3: (@list Z)) (flat1_3: (@list Z)) (rows1_3: (@list (@list Z))) (PreH1 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre )) (PreH2 : (PairedPermutation rows2 rows1_3 lens2 lens1_3 )) (PreH3 : (SameOutsidePairedRange rows2 rows1_3 lens2 lens1_3 (pivot + 1 ) high_pre )) (PreH4 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1 ) high_pre )) (PreH5 : (pivot < high_pre)) (PreH6 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH7 : (PairedPermutation rows1_2 rows2 lens1_2 lens2 )) (PreH8 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1 ) )) (PreH9 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH10 : (pivot > low_pre)) (PreH11 : (0 <= (pivot * number_width_pre ))) (PreH12 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH13 : (0 <= (high_pre * number_width_pre ))) (PreH14 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH15 : (1 <= count_pre)) (PreH16 : (count_pre <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= low_pre)) (PreH20 : (low_pre < high_pre)) (PreH21 : (high_pre < count_pre)) (PreH22 : (low_pre <= pivot)) (PreH23 : (pivot <= high_pre)) (PreH24 : (1 <= (sum (lens)))) (PreH25 : ((sum (lens)) <= 200)) (PreH26 : ((Zlength (rows1_2)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH29 : (Forall (Z.le (1)) lens1_2 )) (PreH30 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH31 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH32 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH33 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH34 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH35 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH36 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre )) (PreH37 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot )) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_3 )
  **  (IntArray.full lengths_pre count_pre lens1_3 )
|--
  EX (lens1: (@list Z))  (flat1: (@list Z))  (rows1: (@list (@list Z))) ,
  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre ) ” 
  &&  “ (GreedySortedRange rows1 lens1 low_pre high_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (lens1_3: (@list Z)) (flat1_3: (@list Z)) (rows1_3: (@list (@list Z))) (PreH1 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre )) (PreH2 : (PairedPermutation rows2 rows1_3 lens2 lens1_3 )) (PreH3 : (SameOutsidePairedRange rows2 rows1_3 lens2 lens1_3 (pivot + 1 ) high_pre )) (PreH4 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1 ) high_pre )) (PreH5 : (pivot < high_pre)) (PreH6 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH7 : (PairedPermutation rows1_2 rows2 lens1_2 lens2 )) (PreH8 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1 ) )) (PreH9 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH10 : (pivot > low_pre)) (PreH11 : (0 <= (pivot * number_width_pre ))) (PreH12 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH13 : (0 <= (high_pre * number_width_pre ))) (PreH14 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH15 : (1 <= count_pre)) (PreH16 : (count_pre <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= low_pre)) (PreH20 : (low_pre < high_pre)) (PreH21 : (high_pre < count_pre)) (PreH22 : (low_pre <= pivot)) (PreH23 : (pivot <= high_pre)) (PreH24 : (1 <= (sum (lens)))) (PreH25 : ((sum (lens)) <= 200)) (PreH26 : ((Zlength (rows1_2)) = count_pre)) (PreH27 : ((Zlength (lens1_2)) = count_pre)) (PreH28 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH29 : (Forall (Z.le (1)) lens1_2 )) (PreH30 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH31 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH32 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH33 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH34 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH35 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH36 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre )) (PreH37 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot )) (PreH38 : ((sum (lens1_2)) = (sum (lens)))) (PreH39 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (FlatRows flat1_3 rows1 (Zlength (rows1_2)) number_width_pre ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1_3 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1_3 low_pre high_pre ) ” 
  &&  “ (GreedySortedRange rows1 lens1_3 low_pre high_pre ) ”
  &&  emp
).

Definition quicksort_numbers_return_wit_2 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot >= high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH3 : (PairedPermutation rows1_2 rows2 lens1_2 lens2 )) (PreH4 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1 ) )) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH6 : (pivot > low_pre)) (PreH7 : (0 <= (pivot * number_width_pre ))) (PreH8 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH9 : (0 <= (high_pre * number_width_pre ))) (PreH10 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : (0 <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH25 : (Forall (Z.le (1)) lens1_2 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH31 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH32 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre )) (PreH33 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot )) (PreH34 : ((sum (lens1_2)) = (sum (lens)))) (PreH35 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
|--
  EX (lens1: (@list Z))  (flat1: (@list Z))  (rows1: (@list (@list Z))) ,
  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre ) ” 
  &&  “ (GreedySortedRange rows1 lens1 low_pre high_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot >= high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH3 : (PairedPermutation rows1_2 rows2 lens1_2 lens2 )) (PreH4 : (SameOutsidePairedRange rows1_2 rows2 lens1_2 lens2 low_pre (pivot - 1 ) )) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH6 : (pivot > low_pre)) (PreH7 : (0 <= (pivot * number_width_pre ))) (PreH8 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH9 : (0 <= (high_pre * number_width_pre ))) (PreH10 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : (0 <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH25 : (Forall (Z.le (1)) lens1_2 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH31 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH32 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre )) (PreH33 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot )) (PreH34 : ((sum (lens1_2)) = (sum (lens)))) (PreH35 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (FlatRows flat2 rows1 (Zlength (rows1_2)) number_width_pre ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens2 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens2 low_pre high_pre ) ” 
  &&  “ (GreedySortedRange rows1 lens2 low_pre high_pre ) ”
  &&  emp
).

Definition quicksort_numbers_return_wit_3 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (lens1_3: (@list Z)) (flat1_3: (@list Z)) (rows1_3: (@list (@list Z))) (PreH1 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre )) (PreH2 : (PairedPermutation rows1_2 rows1_3 lens1_2 lens1_3 )) (PreH3 : (SameOutsidePairedRange rows1_2 rows1_3 lens1_2 lens1_3 (pivot + 1 ) high_pre )) (PreH4 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1 ) high_pre )) (PreH5 : (pivot < high_pre)) (PreH6 : (pivot <= low_pre)) (PreH7 : (0 <= (pivot * number_width_pre ))) (PreH8 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH9 : (0 <= (high_pre * number_width_pre ))) (PreH10 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : (0 <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH25 : (Forall (Z.le (1)) lens1_2 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH31 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH32 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre )) (PreH33 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot )) (PreH34 : ((sum (lens1_2)) = (sum (lens)))) (PreH35 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_3 )
  **  (IntArray.full lengths_pre count_pre lens1_3 )
|--
  EX (lens1: (@list Z))  (flat1: (@list Z))  (rows1: (@list (@list Z))) ,
  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre ) ” 
  &&  “ (GreedySortedRange rows1 lens1 low_pre high_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1_2: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (lens1_3: (@list Z)) (flat1_3: (@list Z)) (rows1_3: (@list (@list Z))) (PreH1 : (FlatRows flat1_3 rows1_3 count_pre number_width_pre )) (PreH2 : (PairedPermutation rows1_2 rows1_3 lens1_2 lens1_3 )) (PreH3 : (SameOutsidePairedRange rows1_2 rows1_3 lens1_2 lens1_3 (pivot + 1 ) high_pre )) (PreH4 : (GreedySortedRange rows1_3 lens1_3 (pivot + 1 ) high_pre )) (PreH5 : (pivot < high_pre)) (PreH6 : (pivot <= low_pre)) (PreH7 : (0 <= (pivot * number_width_pre ))) (PreH8 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH9 : (0 <= (high_pre * number_width_pre ))) (PreH10 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : (0 <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1_2)) = count_pre)) (PreH23 : ((Zlength (lens1_2)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH25 : (Forall (Z.le (1)) lens1_2 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH31 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH32 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 low_pre high_pre )) (PreH33 : (GreedyPartitionedAt rows1_2 lens1_2 low_pre high_pre pivot )) (PreH34 : ((sum (lens1_2)) = (sum (lens)))) (PreH35 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (FlatRows flat1_3 rows1 (Zlength (rows1_2)) number_width_pre ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1_3 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1_3 low_pre high_pre ) ” 
  &&  “ (GreedySortedRange rows1 lens1_3 low_pre high_pre ) ”
  &&  emp
).

Definition quicksort_numbers_return_wit_4 := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (low_pre >= high_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= count_pre)) (PreH9 : ((-1) <= high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : ((Zlength (rows)) = count_pre)) (PreH14 : ((Zlength (lens)) = count_pre)) (PreH15 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH16 : (Forall (Z.le (1)) lens )) (PreH17 : (Forall (Z.ge (number_width_pre)) lens )) (PreH18 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH19 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH20 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH21 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH22 : (FlatRows flat rows count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
|--
  EX (lens1: (@list Z))  (flat1: (@list Z))  (rows1: (@list (@list Z))) ,
  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre ) ” 
  &&  “ (GreedySortedRange rows1 lens1 low_pre high_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (low_pre >= high_pre)) (PreH2 : (0 <= low_pre)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= low_pre)) (PreH8 : (low_pre <= count_pre)) (PreH9 : ((-1) <= high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : (1 <= (sum (lens)))) (PreH12 : ((sum (lens)) <= 200)) (PreH13 : ((Zlength (rows)) = count_pre)) (PreH14 : ((Zlength (lens)) = count_pre)) (PreH15 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH16 : (Forall (Z.le (1)) lens )) (PreH17 : (Forall (Z.ge (number_width_pre)) lens )) (PreH18 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH19 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH20 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH21 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH22 : (FlatRows flat rows count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (FlatRows flat rows1 (Zlength (rows)) number_width_pre ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens low_pre high_pre ) ” 
  &&  “ (GreedySortedRange rows1 lens low_pre high_pre ) ”
  &&  emp
).

Definition quicksort_numbers_partial_solve_wit_1 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (high_pre < count_pre)) (PreH2 : (low_pre < high_pre)) (PreH3 : (0 <= low_pre)) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre <= count_pre)) (PreH10 : ((-1) <= high_pre)) (PreH11 : (high_pre < count_pre)) (PreH12 : (1 <= (sum (lens)))) (PreH13 : ((sum (lens)) <= 200)) (PreH14 : ((Zlength (rows)) = count_pre)) (PreH15 : ((Zlength (lens)) = count_pre)) (PreH16 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH17 : (Forall (Z.le (1)) lens )) (PreH18 : (Forall (Z.ge (number_width_pre)) lens )) (PreH19 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH20 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH21 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH22 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
|--
  “ (high_pre < count_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= count_pre) ” 
  &&  “ ((-1) <= high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Zlength (rows)) = count_pre) ” 
  &&  “ ((Zlength (lens)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows)) ) ” 
  &&  “ (Forall (Z.le (1)) lens ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ”
  &&  (((lengths_pre + (high_pre * sizeof(INT)))) # Int  |-> (Znth high_pre lens 0))
  **  (IntArray.missing_i lengths_pre high_pre 0 count_pre lens )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
.

Definition quicksort_numbers_partial_solve_wit_2 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (scan: Z) (boundary: Z) (PreH1 : (scan < high_pre)) (PreH2 : (0 <= (high_pre * number_width_pre ))) (PreH3 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (0 <= low_pre)) (PreH9 : (low_pre < high_pre)) (PreH10 : (high_pre < count_pre)) (PreH11 : ((low_pre - 1 ) <= boundary)) (PreH12 : (boundary < scan)) (PreH13 : (low_pre <= scan)) (PreH14 : (scan <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH18 : (1 <= pivot_length)) (PreH19 : (pivot_length <= number_width_pre)) (PreH20 : ((Zlength (rows1)) = count_pre)) (PreH21 : ((Zlength (lens1)) = count_pre)) (PreH22 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH23 : (Forall (Z.le (1)) lens1 )) (PreH24 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH25 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH26 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH27 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH28 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH29 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (scan < high_pre) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan <= high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (((lengths_pre + (scan * sizeof(INT)))) # Int  |-> (Znth scan lens1 0))
  **  (IntArray.missing_i lengths_pre scan 0 count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
.

Definition quicksort_numbers_partial_solve_wit_3 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position < current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (position < current_length) ” 
  &&  “ (position < total_length) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ (comparison = 0) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= total_length) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre position ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((scan * number_width_pre ) + position ) * sizeof(INT)))) # Int  |-> (Znth ((scan * number_width_pre ) + position ) flat1 0))
  **  (IntArray.missing_i numbers_pre ((scan * number_width_pre ) + position ) 0 (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_4 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (rows1: (@list (@list Z))) (position: Z) (comparison: Z) (total_length: Z) (current_length: Z) (lens1: (@list Z)) (pivot_length: Z) (boundary: Z) (scan: Z) (PreH1 : (position >= current_length)) (PreH2 : (position < total_length)) (PreH3 : (0 <= (scan * number_width_pre ))) (PreH4 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : ((low_pre - 1 ) <= boundary)) (PreH15 : (boundary < scan)) (PreH16 : (low_pre <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (1 <= (sum (lens)))) (PreH19 : ((sum (lens)) <= 200)) (PreH20 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH21 : (current_length = (Znth (scan) (lens1) (0)))) (PreH22 : (1 <= current_length)) (PreH23 : (current_length <= number_width_pre)) (PreH24 : (1 <= pivot_length)) (PreH25 : (pivot_length <= number_width_pre)) (PreH26 : (total_length = (current_length + pivot_length ))) (PreH27 : (comparison = 0)) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (position >= current_length) ” 
  &&  “ (position < total_length) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ (comparison = 0) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= total_length) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre position ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre ) + (position - current_length ) ) * sizeof(INT)))) # Int  |-> (Znth ((high_pre * number_width_pre ) + (position - current_length ) ) flat1 0))
  **  (IntArray.missing_i numbers_pre ((high_pre * number_width_pre ) + (position - current_length ) ) 0 (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_5 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position < pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (position < pivot_length) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ (comparison = 0) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre position ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre ) + position ) * sizeof(INT)))) # Int  |-> (Znth ((high_pre * number_width_pre ) + position ) flat1 0))
  **  (IntArray.missing_i numbers_pre ((high_pre * number_width_pre ) + position ) 0 (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_6 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (scan: Z) (boundary: Z) (pivot_length: Z) (current_length: Z) (total_length: Z) (comparison: Z) (position: Z) (left_digit: Z) (PreH1 : (position >= pivot_length)) (PreH2 : (0 <= (scan * number_width_pre ))) (PreH3 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : ((low_pre - 1 ) <= boundary)) (PreH14 : (boundary < scan)) (PreH15 : (low_pre <= scan)) (PreH16 : (scan < high_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (current_length = (Znth (scan) (lens1) (0)))) (PreH21 : (1 <= current_length)) (PreH22 : (current_length <= number_width_pre)) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : (total_length = (current_length + pivot_length ))) (PreH26 : (comparison = 0)) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position)))) (PreH30 : ((Zlength (rows1)) = count_pre)) (PreH31 : ((Zlength (lens1)) = count_pre)) (PreH32 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH33 : (Forall (Z.le (1)) lens1 )) (PreH34 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH35 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH36 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH37 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH38 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH39 : (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan )) (PreH40 : (ConcatComparePrefix rows1 lens1 scan high_pre position )) (PreH41 : ((sum (lens1)) = (sum (lens)))) (PreH42 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (position >= pivot_length) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ ((low_pre - 1 ) <= boundary) ” 
  &&  “ (boundary < scan) ” 
  &&  “ (low_pre <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (current_length = (Znth (scan) (lens1) (0))) ” 
  &&  “ (1 <= current_length) ” 
  &&  “ (current_length <= number_width_pre) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ (total_length = (current_length + pivot_length )) ” 
  &&  “ (comparison = 0) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_digit = (ConcatLeftDigit (rows1) (lens1) (scan) (high_pre) (position))) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows1 lens lens1 low_pre high_pre boundary scan ) ” 
  &&  “ (ConcatComparePrefix rows1 lens1 scan high_pre position ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((scan * number_width_pre ) + (position - pivot_length ) ) * sizeof(INT)))) # Int  |-> (Znth ((scan * number_width_pre ) + (position - pivot_length ) ) flat1 0))
  **  (IntArray.missing_i numbers_pre ((scan * number_width_pre ) + (position - pivot_length ) ) 0 (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_7 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column < number_width_pre) ” 
  &&  “ (0 <= (boundary * number_width_pre )) ” 
  &&  “ (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((boundary * number_width_pre ) + column ) * sizeof(INT)))) # Int  |-> (Znth ((boundary * number_width_pre ) + column ) flat_now 0))
  **  (IntArray.missing_i numbers_pre ((boundary * number_width_pre ) + column ) 0 (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_8 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column < number_width_pre) ” 
  &&  “ (0 <= (boundary * number_width_pre )) ” 
  &&  “ (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((scan * number_width_pre ) + column ) * sizeof(INT)))) # Int  |-> (Znth ((scan * number_width_pre ) + column ) flat_now 0))
  **  (IntArray.missing_i numbers_pre ((scan * number_width_pre ) + column ) 0 (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_9 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column < number_width_pre) ” 
  &&  “ (0 <= (boundary * number_width_pre )) ” 
  &&  “ (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((boundary * number_width_pre ) + column ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i numbers_pre ((boundary * number_width_pre ) + column ) 0 (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_10 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((boundary * number_width_pre ) + column )) ((Znth ((scan * number_width_pre ) + column ) flat_now 0)) (flat_now)) )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column < number_width_pre) ” 
  &&  “ (0 <= (boundary * number_width_pre )) ” 
  &&  “ (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((scan * number_width_pre ) + column ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i numbers_pre ((scan * number_width_pre ) + column ) 0 (count_pre * number_width_pre ) (replace_Znth (((boundary * number_width_pre ) + column )) ((Znth ((scan * number_width_pre ) + column ) flat_now 0)) (flat_now)) )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_11 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column >= number_width_pre) ” 
  &&  “ (0 <= (boundary * number_width_pre )) ” 
  &&  “ (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((lengths_pre + (boundary * sizeof(INT)))) # Int  |-> (Znth boundary lens1 0))
  **  (IntArray.missing_i lengths_pre boundary 0 count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
.

Definition quicksort_numbers_partial_solve_wit_12 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
|--
  “ (column >= number_width_pre) ” 
  &&  “ (0 <= (boundary * number_width_pre )) ” 
  &&  “ (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((lengths_pre + (scan * sizeof(INT)))) # Int  |-> (Znth scan lens1 0))
  **  (IntArray.missing_i lengths_pre scan 0 count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
.

Definition quicksort_numbers_partial_solve_wit_13 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
|--
  “ (column >= number_width_pre) ” 
  &&  “ (0 <= (boundary * number_width_pre )) ” 
  &&  “ (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((lengths_pre + (boundary * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i lengths_pre boundary 0 count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
.

Definition quicksort_numbers_partial_solve_wit_14 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (comparison: Z) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (scan: Z) (boundary: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (boundary * number_width_pre ))) (PreH3 : (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (scan * number_width_pre ))) (PreH5 : (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (0 <= (high_pre * number_width_pre ))) (PreH7 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH8 : (1 <= count_pre)) (PreH9 : (count_pre <= 20)) (PreH10 : (1 <= number_width_pre)) (PreH11 : (number_width_pre <= 10)) (PreH12 : (0 <= low_pre)) (PreH13 : (low_pre < high_pre)) (PreH14 : (high_pre < count_pre)) (PreH15 : (low_pre <= boundary)) (PreH16 : (boundary <= scan)) (PreH17 : (scan < high_pre)) (PreH18 : (0 <= column)) (PreH19 : (column <= number_width_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH23 : (1 <= pivot_length)) (PreH24 : (pivot_length <= number_width_pre)) (PreH25 : ((Zlength (rows_before)) = count_pre)) (PreH26 : ((Zlength (lens1)) = count_pre)) (PreH27 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH28 : (Forall (Z.le (1)) lens1 )) (PreH29 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH30 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH31 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH32 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH33 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH34 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan )) (PreH35 : (ConcatCompareOutcome rows_before lens1 scan high_pre comparison )) (PreH36 : (comparison > 0)) (PreH37 : (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre )) (PreH38 : ((sum (lens1)) = (sum (lens)))) (PreH39 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre (replace_Znth (boundary) ((Znth scan lens1 0)) (lens1)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
|--
  “ (column >= number_width_pre) ” 
  &&  “ (0 <= (boundary * number_width_pre )) ” 
  &&  “ (((boundary * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (scan * number_width_pre )) ” 
  &&  “ (((scan * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= boundary) ” 
  &&  “ (boundary <= scan) ” 
  &&  “ (scan < high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (boundary - 1 ) scan ) ” 
  &&  “ (ConcatCompareOutcome rows_before lens1 scan high_pre comparison ) ” 
  &&  “ (comparison > 0) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now boundary scan column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((lengths_pre + (scan * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i lengths_pre scan 0 count_pre (replace_Znth (boundary) ((Znth scan lens1 0)) (lens1)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
.

Definition quicksort_numbers_partial_solve_wit_15 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column < number_width_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((pivot * number_width_pre ) + column ) * sizeof(INT)))) # Int  |-> (Znth ((pivot * number_width_pre ) + column ) flat_now 0))
  **  (IntArray.missing_i numbers_pre ((pivot * number_width_pre ) + column ) 0 (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_16 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column < number_width_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre ) + column ) * sizeof(INT)))) # Int  |-> (Znth ((high_pre * number_width_pre ) + column ) flat_now 0))
  **  (IntArray.missing_i numbers_pre ((high_pre * number_width_pre ) + column ) 0 (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_17 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column < number_width_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((pivot * number_width_pre ) + column ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i numbers_pre ((pivot * number_width_pre ) + column ) 0 (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_18 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column < number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) (replace_Znth (((pivot * number_width_pre ) + column )) ((Znth ((high_pre * number_width_pre ) + column ) flat_now 0)) (flat_now)) )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column < number_width_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((high_pre * number_width_pre ) + column ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i numbers_pre ((high_pre * number_width_pre ) + column ) 0 (count_pre * number_width_pre ) (replace_Znth (((pivot * number_width_pre ) + column )) ((Znth ((high_pre * number_width_pre ) + column ) flat_now 0)) (flat_now)) )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_19 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (column >= number_width_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((lengths_pre + (pivot * sizeof(INT)))) # Int  |-> (Znth pivot lens1 0))
  **  (IntArray.missing_i lengths_pre pivot 0 count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
.

Definition quicksort_numbers_partial_solve_wit_20 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
|--
  “ (column >= number_width_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((lengths_pre + (high_pre * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i lengths_pre high_pre 0 count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
.

Definition quicksort_numbers_partial_solve_wit_21 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat_now: (@list Z)) (rows_now: (@list (@list Z))) (rows_before: (@list (@list Z))) (lens1: (@list Z)) (pivot_length: Z) (column: Z) (pivot: Z) (PreH1 : (column >= number_width_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (0 <= column)) (PreH16 : (column <= number_width_pre)) (PreH17 : (1 <= (sum (lens)))) (PreH18 : ((sum (lens)) <= 200)) (PreH19 : (pivot_length = (Znth (high_pre) (lens1) (0)))) (PreH20 : (1 <= pivot_length)) (PreH21 : (pivot_length <= number_width_pre)) (PreH22 : ((Zlength (rows_before)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) )) (PreH31 : (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre )) (PreH32 : (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre )) (PreH33 : ((sum (lens1)) = (sum (lens)))) (PreH34 : (FlatRows flat_now rows_now count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre (replace_Znth (high_pre) ((Znth pivot lens1 0)) (lens1)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
|--
  “ (column >= number_width_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (0 <= column) ” 
  &&  “ (column <= number_width_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (pivot_length = (Znth (high_pre) (lens1) (0))) ” 
  &&  “ (1 <= pivot_length) ” 
  &&  “ (pivot_length <= number_width_pre) ” 
  &&  “ ((Zlength (rows_before)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows_before)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows_before) (lens1)) ) ” 
  &&  “ (PartitionScanState rows rows_before lens lens1 low_pre high_pre (pivot - 1 ) high_pre ) ” 
  &&  “ (SwapRowsPrefix rows_before rows_now pivot high_pre column number_width_pre ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat_now rows_now count_pre number_width_pre ) ”
  &&  (((lengths_pre + (pivot * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i lengths_pre pivot 0 count_pre (replace_Znth (high_pre) ((Znth pivot lens1 0)) (lens1)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat_now )
.

Definition quicksort_numbers_partial_solve_wit_22_pure := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (PreH1 : (pivot > low_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH28 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= count_pre) ” 
  &&  “ ((-1) <= (pivot - 1 )) ” 
  &&  “ ((pivot - 1 ) < count_pre) ” 
  &&  “ (1 <= (sum (lens1))) ” 
  &&  “ ((sum (lens1)) <= 200) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
.

Definition quicksort_numbers_partial_solve_wit_22_aux := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (PreH1 : (pivot > low_pre)) (PreH2 : (0 <= (pivot * number_width_pre ))) (PreH3 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : (0 <= (high_pre * number_width_pre ))) (PreH5 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (0 <= low_pre)) (PreH11 : (low_pre < high_pre)) (PreH12 : (high_pre < count_pre)) (PreH13 : (low_pre <= pivot)) (PreH14 : (pivot <= high_pre)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH28 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH29 : ((sum (lens1)) = (sum (lens)))) (PreH30 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre <= count_pre) ” 
  &&  “ ((-1) <= (pivot - 1 )) ” 
  &&  “ ((pivot - 1 ) < count_pre) ” 
  &&  “ (1 <= (sum (lens1))) ” 
  &&  “ ((sum (lens1)) <= 200) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ” 
  &&  “ (pivot > low_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre ) ” 
  &&  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_22 := quicksort_numbers_partial_solve_wit_22_pure -> quicksort_numbers_partial_solve_wit_22_aux.

Definition quicksort_numbers_partial_solve_wit_23_pure := 
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot < high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH3 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH4 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH6 : (pivot > low_pre)) (PreH7 : (0 <= (pivot * number_width_pre ))) (PreH8 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH9 : (0 <= (high_pre * number_width_pre ))) (PreH10 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : (0 <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH31 : (PairedPermutation rows rows1 lens lens1 )) (PreH32 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH33 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH34 : ((sum (lens1)) = (sum (lens)))) (PreH35 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= count_pre) ” 
  &&  “ ((-1) <= high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (FlatRows flat2 rows2 count_pre number_width_pre ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows2) (lens2)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows2) (lens2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows2)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows2)) ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens2 ) ” 
  &&  “ (Forall (Z.le (1)) lens2 ) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows2)) ) ” 
  &&  “ ((Zlength (lens2)) = count_pre) ” 
  &&  “ ((Zlength (rows2)) = count_pre) ” 
  &&  “ ((sum (lens2)) <= 200) ” 
  &&  “ (1 <= (sum (lens2))) ”
) \/
(
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (1 <= (sum (lens2))) ” 
  &&  “ ((sum (lens2)) <= 200) ” 
  &&  “ ((Zlength (rows2)) = count_pre) ” 
  &&  “ ((Zlength (lens2)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows2)) ) ” 
  &&  “ (Forall (Z.le (1)) lens2 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens2 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows2)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows2) (lens2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows2) (lens2)) ) ”
).

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_1 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (1 <= (sum (lens2))) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_2 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ ((sum (lens2)) <= 200) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_3 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ ((Zlength (rows2)) = count_pre) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_4 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ ((Zlength (lens2)) = count_pre) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_5 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows2)) ) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_6 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (Forall (Z.le (1)) lens2 ) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_7 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (Forall (Z.ge (number_width_pre)) lens2 ) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_8 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (Forall (Z.le (1)) (map ((hd (0))) (rows2)) ) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_9 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows2)) ) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_10 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (Forall (Z.le (0)) (concatenate_rows (rows2) (lens2)) ) ”
.

Definition quicksort_numbers_partial_solve_wit_23_pure_split_goal_11 := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot <= INT_MAX)) (PreH2 : (high_pre <= INT_MAX)) (PreH3 : (low_pre <= INT_MAX)) (PreH4 : (number_width_pre <= INT_MAX)) (PreH5 : (count_pre <= INT_MAX)) (PreH6 : (pivot >= INT_MIN)) (PreH7 : (high_pre >= INT_MIN)) (PreH8 : (low_pre >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (count_pre >= INT_MIN)) (PreH11 : (pivot < high_pre)) (PreH12 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH13 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH14 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH15 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH16 : (pivot > low_pre)) (PreH17 : (0 <= (pivot * number_width_pre ))) (PreH18 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH19 : (0 <= (high_pre * number_width_pre ))) (PreH20 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (0 <= low_pre)) (PreH26 : (low_pre < high_pre)) (PreH27 : (high_pre < count_pre)) (PreH28 : (low_pre <= pivot)) (PreH29 : (pivot <= high_pre)) (PreH30 : (1 <= (sum (lens)))) (PreH31 : ((sum (lens)) <= 200)) (PreH32 : ((Zlength (rows1)) = count_pre)) (PreH33 : ((Zlength (lens1)) = count_pre)) (PreH34 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH35 : (Forall (Z.le (1)) lens1 )) (PreH36 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH37 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH38 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH39 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH40 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH41 : (PairedPermutation rows rows1 lens lens1 )) (PreH42 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH43 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH44 : ((sum (lens1)) = (sum (lens)))) (PreH45 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (Forall (Z.ge (9)) (concatenate_rows (rows2) (lens2)) ) ”
.

Definition quicksort_numbers_partial_solve_wit_23_aux := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows2: (@list (@list Z))) (lens2: (@list Z)) (flat2: (@list Z)) (PreH1 : (pivot < high_pre)) (PreH2 : (FlatRows flat2 rows2 count_pre number_width_pre )) (PreH3 : (PairedPermutation rows1 rows2 lens1 lens2 )) (PreH4 : (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) )) (PreH5 : (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) )) (PreH6 : (pivot > low_pre)) (PreH7 : (0 <= (pivot * number_width_pre ))) (PreH8 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH9 : (0 <= (high_pre * number_width_pre ))) (PreH10 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : (0 <= low_pre)) (PreH16 : (low_pre < high_pre)) (PreH17 : (high_pre < count_pre)) (PreH18 : (low_pre <= pivot)) (PreH19 : (pivot <= high_pre)) (PreH20 : (1 <= (sum (lens)))) (PreH21 : ((sum (lens)) <= 200)) (PreH22 : ((Zlength (rows1)) = count_pre)) (PreH23 : ((Zlength (lens1)) = count_pre)) (PreH24 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH25 : (Forall (Z.le (1)) lens1 )) (PreH26 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH27 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH28 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH29 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH30 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH31 : (PairedPermutation rows rows1 lens lens1 )) (PreH32 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH33 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH34 : ((sum (lens1)) = (sum (lens)))) (PreH35 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= count_pre) ” 
  &&  “ ((-1) <= high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (FlatRows flat2 rows2 count_pre number_width_pre ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows2) (lens2)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows2) (lens2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows2)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows2)) ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens2 ) ” 
  &&  “ (Forall (Z.le (1)) lens2 ) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows2)) ) ” 
  &&  “ ((Zlength (lens2)) = count_pre) ” 
  &&  “ ((Zlength (rows2)) = count_pre) ” 
  &&  “ ((sum (lens2)) <= 200) ” 
  &&  “ (1 <= (sum (lens2))) ” 
  &&  “ (pivot < high_pre) ” 
  &&  “ (FlatRows flat2 rows2 count_pre number_width_pre ) ” 
  &&  “ (PairedPermutation rows1 rows2 lens1 lens2 ) ” 
  &&  “ (SameOutsidePairedRange rows1 rows2 lens1 lens2 low_pre (pivot - 1 ) ) ” 
  &&  “ (GreedySortedRange rows2 lens2 low_pre (pivot - 1 ) ) ” 
  &&  “ (pivot > low_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre ) ” 
  &&  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat2 )
  **  (IntArray.full lengths_pre count_pre lens2 )
.

Definition quicksort_numbers_partial_solve_wit_23 := quicksort_numbers_partial_solve_wit_23_pure -> quicksort_numbers_partial_solve_wit_23_aux.

Definition quicksort_numbers_partial_solve_wit_24_pure := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (0 <= (pivot * number_width_pre ))) (PreH4 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH21 : (Forall (Z.le (1)) lens1 )) (PreH22 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH23 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH25 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH27 : (PairedPermutation rows rows1 lens lens1 )) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "low" ) )) # Int  |-> low_pre)
  **  ((( &( "high" ) )) # Int  |-> high_pre)
  **  ((( &( "pivot" ) )) # Int  |-> pivot)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "scan" ) )) # Int  |->_)
  **  ((( &( "boundary" ) )) # Int  |->_)
  **  ((( &( "pivot_length" ) )) # Int  |->_)
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= count_pre) ” 
  &&  “ ((-1) <= high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (1 <= (sum (lens1))) ” 
  &&  “ ((sum (lens1)) <= 200) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
.

Definition quicksort_numbers_partial_solve_wit_24_aux := 
forall (high_pre: Z) (low_pre: Z) (number_width_pre: Z) (count_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (pivot: Z) (rows1: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (PreH1 : (pivot < high_pre)) (PreH2 : (pivot <= low_pre)) (PreH3 : (0 <= (pivot * number_width_pre ))) (PreH4 : (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH5 : (0 <= (high_pre * number_width_pre ))) (PreH6 : (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH7 : (1 <= count_pre)) (PreH8 : (count_pre <= 20)) (PreH9 : (1 <= number_width_pre)) (PreH10 : (number_width_pre <= 10)) (PreH11 : (0 <= low_pre)) (PreH12 : (low_pre < high_pre)) (PreH13 : (high_pre < count_pre)) (PreH14 : (low_pre <= pivot)) (PreH15 : (pivot <= high_pre)) (PreH16 : (1 <= (sum (lens)))) (PreH17 : ((sum (lens)) <= 200)) (PreH18 : ((Zlength (rows1)) = count_pre)) (PreH19 : ((Zlength (lens1)) = count_pre)) (PreH20 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH21 : (Forall (Z.le (1)) lens1 )) (PreH22 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH23 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH25 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH27 : (PairedPermutation rows rows1 lens lens1 )) (PreH28 : (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre )) (PreH29 : (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot )) (PreH30 : ((sum (lens1)) = (sum (lens)))) (PreH31 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= (pivot + 1 )) ” 
  &&  “ ((pivot + 1 ) <= count_pre) ” 
  &&  “ ((-1) <= high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (1 <= (sum (lens1))) ” 
  &&  “ ((sum (lens1)) <= 200) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ” 
  &&  “ (pivot < high_pre) ” 
  &&  “ (pivot <= low_pre) ” 
  &&  “ (0 <= (pivot * number_width_pre )) ” 
  &&  “ (((pivot * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (0 <= (high_pre * number_width_pre )) ” 
  &&  “ (((high_pre * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= low_pre) ” 
  &&  “ (low_pre < high_pre) ” 
  &&  “ (high_pre < count_pre) ” 
  &&  “ (low_pre <= pivot) ” 
  &&  “ (pivot <= high_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (SameOutsidePairedRange rows rows1 lens lens1 low_pre high_pre ) ” 
  &&  “ (GreedyPartitionedAt rows1 lens1 low_pre high_pre pivot ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
.

Definition quicksort_numbers_partial_solve_wit_24 := quicksort_numbers_partial_solve_wit_24_pure -> quicksort_numbers_partial_solve_wit_24_aux.

(*----- Function concatenating_numbers -----*)

Definition concatenating_numbers_safety_wit_1 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH10 : (Forall (Z.le (1)) lens )) (PreH11 : (Forall (Z.ge (number_width_pre)) lens )) (PreH12 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH13 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH15 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "result_length" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_safety_wit_2 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH10 : (Forall (Z.le (1)) lens )) (PreH11 : (Forall (Z.ge (number_width_pre)) lens )) (PreH12 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH13 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH15 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "result_length" ) )) # Int  |-> 0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenating_numbers_safety_wit_3 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH11 : (Forall (Z.le (1)) lens )) (PreH12 : (Forall (Z.ge (number_width_pre)) lens )) (PreH13 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH15 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH16 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "result_length" ) )) # Int  |-> 0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((count_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count_pre - 1 )) ”
.

Definition concatenating_numbers_safety_wit_4 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH11 : (Forall (Z.le (1)) lens )) (PreH12 : (Forall (Z.ge (number_width_pre)) lens )) (PreH13 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH15 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH16 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "result_length" ) )) # Int  |-> 0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_safety_wit_5 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH11 : (Forall (Z.le (1)) lens )) (PreH12 : (Forall (Z.ge (number_width_pre)) lens )) (PreH13 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH15 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH16 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "result_length" ) )) # Int  |-> 0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenating_numbers_safety_wit_6 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (lens1: (@list Z)) (flat1: (@list Z)) (rows1: (@list (@list Z))) (PreH1 : (FlatRows flat1 rows1 count_pre number_width_pre )) (PreH2 : (PairedPermutation rows rows1 lens lens1 )) (PreH3 : (SameOutsidePairedRange rows rows1 lens lens1 0 (count_pre - 1 ) )) (PreH4 : (GreedySortedRange rows1 lens1 0 (count_pre - 1 ) )) (PreH5 : (count_pre > 1)) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : ((Zlength (rows)) = count_pre)) (PreH13 : ((Zlength (lens)) = count_pre)) (PreH14 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH15 : (Forall (Z.le (1)) lens )) (PreH16 : (Forall (Z.ge (number_width_pre)) lens )) (PreH17 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH18 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH19 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH20 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH21 : (FlatRows flat rows count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "result_length" ) )) # Int  |-> 0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_safety_wit_7 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (count_pre <= 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH11 : (Forall (Z.le (1)) lens )) (PreH12 : (Forall (Z.ge (number_width_pre)) lens )) (PreH13 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH15 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH16 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "result_length" ) )) # Int  |-> 0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_safety_wit_8 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (result_length: Z) (output: (@list Z)) (lens1: (@list Z)) (rows1: (@list (@list Z))) (i: Z) (PreH1 : (i < count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (0 <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1)) = count_pre)) (PreH11 : ((Zlength (lens1)) = count_pre)) (PreH12 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH13 : (Forall (Z.le (1)) lens1 )) (PreH14 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH15 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH16 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH17 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH18 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH19 : (PairedPermutation rows rows1 lens lens1 )) (PreH20 : (GreedySorted rows1 lens1 )) (PreH21 : ((sum (lens1)) = (sum (lens)))) (PreH22 : (output = (ConcatenatedPrefix (rows1) (lens1) (i)))) (PreH23 : (result_length = (Zlength (output)))) (PreH24 : (0 <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_safety_wit_9 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (output: (@list Z)) (rows1: (@list (@list Z))) (result_length: Z) (lens1: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < (Znth i lens1 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1) (0)))) (PreH15 : (1 <= (Znth (i) (lens1) (0)))) (PreH16 : ((Znth (i) (lens1) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (GreedySorted rows1 lens1 )) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (((i * number_width_pre ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * number_width_pre ) + j )) ”
.

Definition concatenating_numbers_safety_wit_10 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (output: (@list Z)) (rows1: (@list (@list Z))) (result_length: Z) (lens1: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < (Znth i lens1 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1) (0)))) (PreH15 : (1 <= (Znth (i) (lens1) (0)))) (PreH16 : ((Znth (i) (lens1) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (GreedySorted rows1 lens1 )) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ ((i * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * number_width_pre )) ”
.

Definition concatenating_numbers_safety_wit_11 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (output: (@list Z)) (rows1: (@list (@list Z))) (result_length: Z) (lens1: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < (Znth i lens1 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1) (0)))) (PreH15 : (1 <= (Znth (i) (lens1) (0)))) (PreH16 : ((Znth (i) (lens1) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (GreedySorted rows1 lens1 )) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.seg result_pre 0 (result_length + 1 ) (app (output) ((cons ((Znth ((i * number_width_pre ) + j ) flat1 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
|--
  “ ((result_length + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result_length + 1 )) ”
.

Definition concatenating_numbers_safety_wit_12 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (output: (@list Z)) (rows1: (@list (@list Z))) (result_length: Z) (lens1: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < (Znth i lens1 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1) (0)))) (PreH15 : (1 <= (Znth (i) (lens1) (0)))) (PreH16 : ((Znth (i) (lens1) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (GreedySorted rows1 lens1 )) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.seg result_pre 0 (result_length + 1 ) (app (output) ((cons ((Znth ((i * number_width_pre ) + j ) flat1 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "result_length" ) )) # Int  |-> (result_length + 1 ))
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition concatenating_numbers_safety_wit_13 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (output: (@list Z)) (rows1: (@list (@list Z))) (result_length: Z) (lens1: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= (Znth i lens1 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1) (0)))) (PreH15 : (1 <= (Znth (i) (lens1) (0)))) (PreH16 : ((Znth (i) (lens1) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (GreedySorted rows1 lens1 )) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens1 )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition concatenating_numbers_entail_wit_1 := 
(
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH10 : (Forall (Z.le (1)) lens )) (PreH11 : (Forall (Z.ge (number_width_pre)) lens )) (PreH12 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH13 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH15 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH16 : (flat = (concat (rows)))) (PreH17 : (Forall (Z.ge (1000000000)) (DecimalRowValues (rows) (lens)) )) ,
  (IntArray2.full numbers_pre count_pre number_width_pre rows )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Zlength (rows)) = count_pre) ” 
  &&  “ ((Zlength (lens)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows)) ) ” 
  &&  “ (Forall (Z.le (1)) lens ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH10 : (Forall (Z.le (1)) lens )) (PreH11 : (Forall (Z.ge (number_width_pre)) lens )) (PreH12 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH13 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH15 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH16 : (flat = (concat (rows)))) (PreH17 : (Forall (Z.ge (1000000000)) (DecimalRowValues (rows) (lens)) )) ,
  (IntArray2.full numbers_pre count_pre number_width_pre rows )
|--
  “ (FlatRows flat rows count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
).

Definition concatenating_numbers_entail_wit_1_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH10 : (Forall (Z.le (1)) lens )) (PreH11 : (Forall (Z.ge (number_width_pre)) lens )) (PreH12 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH13 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH15 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH16 : (flat = (concat (rows)))) (PreH17 : (Forall (Z.ge (1000000000)) (DecimalRowValues (rows) (lens)) )) ,
  (IntArray2.full numbers_pre count_pre number_width_pre rows )
|--
  “ (FlatRows flat rows count_pre number_width_pre ) ”
.

Definition concatenating_numbers_entail_wit_1_split_goal_spatial := 
forall (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (1 <= (sum (lens)))) (PreH6 : ((sum (lens)) <= 200)) (PreH7 : ((Zlength (rows)) = count_pre)) (PreH8 : ((Zlength (lens)) = count_pre)) (PreH9 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH10 : (Forall (Z.le (1)) lens )) (PreH11 : (Forall (Z.ge (number_width_pre)) lens )) (PreH12 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH13 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH15 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH16 : (flat = (concat (rows)))) (PreH17 : (Forall (Z.ge (1000000000)) (DecimalRowValues (rows) (lens)) )) ,
  (IntArray2.full numbers_pre count_pre number_width_pre rows )
|--
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
.

Definition concatenating_numbers_entail_wit_2_1 := 
(
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (rows1_2: (@list (@list Z))) (PreH1 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) (PreH2 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH3 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 0 (count_pre - 1 ) )) (PreH4 : (GreedySortedRange rows1_2 lens1_2 0 (count_pre - 1 ) )) (PreH5 : (count_pre > 1)) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : ((Zlength (rows)) = count_pre)) (PreH13 : ((Zlength (lens)) = count_pre)) (PreH14 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH15 : (Forall (Z.le (1)) lens )) (PreH16 : (Forall (Z.ge (number_width_pre)) lens )) (PreH17 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH18 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH19 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH20 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH21 : (FlatRows flat rows count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (flat1: (@list Z))  (output: (@list Z))  (lens1: (@list Z))  (rows1: (@list (@list Z))) ,
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= count_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (GreedySorted rows1 lens1 ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (output = (ConcatenatedPrefix (rows1) (lens1) (0))) ” 
  &&  “ (0 = (Zlength (output))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 0 output )
  **  (IntArray.undef_seg result_pre 0 (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (lens1_2: (@list Z)) (flat1_2: (@list Z)) (rows1_2: (@list (@list Z))) (PreH1 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) (PreH2 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH3 : (SameOutsidePairedRange rows rows1_2 lens lens1_2 0 (count_pre - 1 ) )) (PreH4 : (GreedySortedRange rows1_2 lens1_2 0 (count_pre - 1 ) )) (PreH5 : (count_pre > 1)) (PreH6 : (1 <= count_pre)) (PreH7 : (count_pre <= 20)) (PreH8 : (1 <= number_width_pre)) (PreH9 : (number_width_pre <= 10)) (PreH10 : (1 <= (sum (lens)))) (PreH11 : ((sum (lens)) <= 200)) (PreH12 : ((Zlength (rows)) = count_pre)) (PreH13 : ((Zlength (lens)) = count_pre)) (PreH14 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH15 : (Forall (Z.le (1)) lens )) (PreH16 : (Forall (Z.ge (number_width_pre)) lens )) (PreH17 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH18 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH19 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH20 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH21 : (FlatRows flat rows count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (rows))) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows))) ” 
  &&  “ ((Zlength (lens1_2)) = (Zlength (rows))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1_2 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1_2 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1_2 ) ” 
  &&  “ (GreedySorted rows1 lens1_2 ) ” 
  &&  “ ((sum (lens1_2)) = (sum (lens))) ” 
  &&  “ ((@nil Z) = (ConcatenatedPrefix (rows1) (lens1_2) (0))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (sum (lens))) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows)) number_width_pre ) ”
  &&  emp
).

Definition concatenating_numbers_entail_wit_2_2 := 
(
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (count_pre <= 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH11 : (Forall (Z.le (1)) lens )) (PreH12 : (Forall (Z.ge (number_width_pre)) lens )) (PreH13 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH15 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH16 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (flat1: (@list Z))  (output: (@list Z))  (lens1: (@list Z))  (rows1: (@list (@list Z))) ,
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= count_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (GreedySorted rows1 lens1 ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (output = (ConcatenatedPrefix (rows1) (lens1) (0))) ” 
  &&  “ (0 = (Zlength (output))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 0 output )
  **  (IntArray.undef_seg result_pre 0 (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (count_pre <= 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH11 : (Forall (Z.le (1)) lens )) (PreH12 : (Forall (Z.ge (number_width_pre)) lens )) (PreH13 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH15 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH16 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (Zlength (rows))) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens ) ” 
  &&  “ (GreedySorted rows1 lens ) ” 
  &&  “ ((@nil Z) = (ConcatenatedPrefix (rows1) (lens) (0))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (sum (lens))) ” 
  &&  “ (FlatRows flat rows1 (Zlength (rows)) number_width_pre ) ”
  &&  emp
).

Definition concatenating_numbers_entail_wit_3 := 
(
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (result_length: Z) (output_2: (@list Z)) (lens1_2: (@list Z)) (rows1_2: (@list (@list Z))) (i: Z) (PreH1 : (i < count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (0 <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1_2)) = count_pre)) (PreH11 : ((Zlength (lens1_2)) = count_pre)) (PreH12 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH13 : (Forall (Z.le (1)) lens1_2 )) (PreH14 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH15 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH16 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH17 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH18 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH19 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH20 : (GreedySorted rows1_2 lens1_2 )) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH23 : (result_length = (Zlength (output_2)))) (PreH24 : (0 <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
  **  (IntArray.seg result_pre 0 result_length output_2 )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  EX (flat1: (@list Z))  (output: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (i * number_width_pre )) ” 
  &&  “ (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ ((0 < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens)))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < count_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Znth (i) (lens1) (0))) ” 
  &&  “ (1 <= (Znth (i) (lens1) (0))) ” 
  &&  “ ((Znth (i) (lens1) (0)) <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (GreedySorted rows1 lens1 ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (0))) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ (result_length <= (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (result_length: Z) (output_2: (@list Z)) (lens1_2: (@list Z)) (rows1_2: (@list (@list Z))) (i: Z) (PreH1 : (i < count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (0 <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1_2)) = count_pre)) (PreH11 : ((Zlength (lens1_2)) = count_pre)) (PreH12 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH13 : (Forall (Z.le (1)) lens1_2 )) (PreH14 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH15 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH16 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH17 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH18 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH19 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH20 : (GreedySorted rows1_2 lens1_2 )) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH23 : (result_length = (Zlength (output_2)))) (PreH24 : (0 <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((ConcatenatedPrefix (rows1_2) (lens1_2) (i)) = (ConcatenatedOutputPrefix (rows1) (lens1_2) (i) (0))) ” 
  &&  “ (0 <= (i * number_width_pre )) ” 
  &&  “ (((i * number_width_pre ) + number_width_pre ) <= ((Zlength (rows1_2)) * number_width_pre )) ” 
  &&  “ ((0 < (Znth (i) (lens1_2) (0))) -> ((Zlength (output_2)) < (sum (lens)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Znth (i) (lens1_2) (0))) ” 
  &&  “ (1 <= (Znth (i) (lens1_2) (0))) ” 
  &&  “ ((Znth (i) (lens1_2) (0)) <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1_2 ) ” 
  &&  “ (GreedySorted rows1 lens1_2 ) ” 
  &&  “ ((Zlength (output_2)) = (Zlength ((ConcatenatedOutputPrefix (rows1) (lens1_2) (i) (0))))) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition concatenating_numbers_entail_wit_4 := 
(
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (output_2: (@list Z)) (rows1_2: (@list (@list Z))) (result_length: Z) (lens1_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < (Znth i lens1_2 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1_2) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1_2) (0)))) (PreH15 : (1 <= (Znth (i) (lens1_2) (0)))) (PreH16 : ((Znth (i) (lens1_2) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1_2)) = count_pre)) (PreH18 : ((Zlength (lens1_2)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH20 : (Forall (Z.le (1)) lens1_2 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH26 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH27 : (GreedySorted rows1_2 lens1_2 )) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH30 : (result_length = (Zlength (output_2)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  (IntArray.seg result_pre 0 (result_length + 1 ) (app (output_2) ((cons ((Znth ((i * number_width_pre ) + j ) flat1_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
|--
  EX (flat1: (@list Z))  (output: (@list Z))  (rows1: (@list (@list Z)))  (lens1: (@list Z)) ,
  “ (0 <= (i * number_width_pre )) ” 
  &&  “ (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ (((j + 1 ) < (Znth (i) (lens1) (0))) -> ((result_length + 1 ) < (sum (lens)))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < count_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Znth (i) (lens1) (0))) ” 
  &&  “ (1 <= (Znth (i) (lens1) (0))) ” 
  &&  “ ((Znth (i) (lens1) (0)) <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (GreedySorted rows1 lens1 ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) ((j + 1 )))) ” 
  &&  “ ((result_length + 1 ) = (Zlength (output))) ” 
  &&  “ (0 <= (result_length + 1 )) ” 
  &&  “ ((result_length + 1 ) <= (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 (result_length + 1 ) output )
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (output_2: (@list Z)) (rows1_2: (@list (@list Z))) (result_length: Z) (lens1_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < (Znth i lens1_2 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1_2) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1_2) (0)))) (PreH15 : (1 <= (Znth (i) (lens1_2) (0)))) (PreH16 : ((Znth (i) (lens1_2) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1_2)) = count_pre)) (PreH18 : ((Zlength (lens1_2)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH20 : (Forall (Z.le (1)) lens1_2 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH26 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH27 : (GreedySorted rows1_2 lens1_2 )) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH30 : (result_length = (Zlength (output_2)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((app ((ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j))) ((cons ((Znth ((i * number_width_pre ) + j ) flat1_2 0)) ((@nil Z))))) = (ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((j + 1 )))) ” 
  &&  “ (((j + 1 ) < (Znth (i) (lens1_2) (0))) -> (((Zlength (output_2)) + 1 ) < (sum (lens)))) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (Znth (i) (lens1_2) (0))) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1_2 ) ” 
  &&  “ (GreedySorted rows1 lens1_2 ) ” 
  &&  “ (((Zlength (output_2)) + 1 ) = (Zlength ((ConcatenatedOutputPrefix (rows1) (lens1_2) (i) ((j + 1 )))))) ” 
  &&  “ (0 <= ((Zlength (output_2)) + 1 )) ” 
  &&  “ (((Zlength (output_2)) + 1 ) <= (sum (lens))) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition concatenating_numbers_entail_wit_5 := 
(
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (output_2: (@list Z)) (rows1_2: (@list (@list Z))) (result_length: Z) (lens1_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= (Znth i lens1_2 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1_2) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1_2) (0)))) (PreH15 : (1 <= (Znth (i) (lens1_2) (0)))) (PreH16 : ((Znth (i) (lens1_2) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1_2)) = count_pre)) (PreH18 : ((Zlength (lens1_2)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH20 : (Forall (Z.le (1)) lens1_2 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH26 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH27 : (GreedySorted rows1_2 lens1_2 )) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH30 : (result_length = (Zlength (output_2)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens1_2 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1_2 )
  **  (IntArray.seg result_pre 0 result_length output_2 )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  EX (flat1: (@list Z))  (output: (@list Z))  (lens1: (@list Z))  (rows1: (@list (@list Z))) ,
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= count_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (GreedySorted rows1 lens1 ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (output = (ConcatenatedPrefix (rows1) (lens1) ((i + 1 )))) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ (result_length <= (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1_2: (@list Z)) (output_2: (@list Z)) (rows1_2: (@list (@list Z))) (result_length: Z) (lens1_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= (Znth i lens1_2 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1_2) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1_2) (0)))) (PreH15 : (1 <= (Znth (i) (lens1_2) (0)))) (PreH16 : ((Znth (i) (lens1_2) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1_2)) = count_pre)) (PreH18 : ((Zlength (lens1_2)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH20 : (Forall (Z.le (1)) lens1_2 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH26 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH27 : (GreedySorted rows1_2 lens1_2 )) (PreH28 : ((sum (lens1_2)) = (sum (lens)))) (PreH29 : (output_2 = (ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)))) (PreH30 : (result_length = (Zlength (output_2)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1_2 rows1_2 count_pre number_width_pre )) ,
  TT && emp 
|--
  EX (rows1: (@list (@list Z))) ,
  “ ((ConcatenatedOutputPrefix (rows1_2) (lens1_2) (i) (j)) = (ConcatenatedPrefix (rows1) (lens1_2) ((i + 1 )))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (Zlength (rows1_2))) ” 
  &&  “ ((Zlength (rows1)) = (Zlength (rows1_2))) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1_2)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1_2 ) ” 
  &&  “ (GreedySorted rows1 lens1_2 ) ” 
  &&  “ ((Zlength (output_2)) = (Zlength ((ConcatenatedPrefix (rows1) (lens1_2) ((i + 1 )))))) ” 
  &&  “ (FlatRows flat1_2 rows1 (Zlength (rows1_2)) number_width_pre ) ”
  &&  emp
).

Definition concatenating_numbers_return_wit_1 := 
(
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (result_length: Z) (output_2: (@list Z)) (lens1_2: (@list Z)) (rows1_2: (@list (@list Z))) (i: Z) (PreH1 : (i >= count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (0 <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1_2)) = count_pre)) (PreH11 : ((Zlength (lens1_2)) = count_pre)) (PreH12 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH13 : (Forall (Z.le (1)) lens1_2 )) (PreH14 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH15 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH16 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH17 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH18 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH19 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH20 : (GreedySorted rows1_2 lens1_2 )) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH23 : (result_length = (Zlength (output_2)))) (PreH24 : (0 <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1_2 )
  **  (IntArray.seg result_pre 0 result_length output_2 )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  EX (lens1: (@list Z))  (rows1: (@list (@list Z)))  (output: (@list Z)) ,
  “ (result_pre = result_pre) ” 
  &&  “ (LargestConcatenation rows lens output ) ”
  &&  (IntArray2.full numbers_pre count_pre number_width_pre rows1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.full result_pre (sum (lens)) output )
) \/
(
forall (result_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (result_length: Z) (output_2: (@list Z)) (lens1_2: (@list Z)) (rows1_2: (@list (@list Z))) (i: Z) (PreH1 : (i >= count_pre)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (0 <= i)) (PreH9 : (i <= count_pre)) (PreH10 : ((Zlength (rows1_2)) = count_pre)) (PreH11 : ((Zlength (lens1_2)) = count_pre)) (PreH12 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1_2)) )) (PreH13 : (Forall (Z.le (1)) lens1_2 )) (PreH14 : (Forall (Z.ge (number_width_pre)) lens1_2 )) (PreH15 : (Forall (Z.le (1)) (map ((hd (0))) (rows1_2)) )) (PreH16 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1_2)) )) (PreH17 : (Forall (Z.le (0)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH18 : (Forall (Z.ge (9)) (concatenate_rows (rows1_2) (lens1_2)) )) (PreH19 : (PairedPermutation rows rows1_2 lens lens1_2 )) (PreH20 : (GreedySorted rows1_2 lens1_2 )) (PreH21 : ((sum (lens1_2)) = (sum (lens)))) (PreH22 : (output_2 = (ConcatenatedPrefix (rows1_2) (lens1_2) (i)))) (PreH23 : (result_length = (Zlength (output_2)))) (PreH24 : (0 <= result_length)) (PreH25 : (result_length <= (sum (lens)))) (PreH26 : (FlatRows flat1 rows1_2 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.seg result_pre 0 result_length output_2 )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  EX (rows1: (@list (@list Z)))  (output: (@list Z)) ,
  “ (LargestConcatenation rows lens output ) ”
  &&  (IntArray2.full numbers_pre count_pre number_width_pre rows1 )
  **  (IntArray.full result_pre (sum (lens)) output )
).

Definition concatenating_numbers_partial_solve_wit_1_pure := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH11 : (Forall (Z.le (1)) lens )) (PreH12 : (Forall (Z.ge (number_width_pre)) lens )) (PreH13 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH15 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH16 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "result_length" ) )) # Int  |-> 0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= count_pre) ” 
  &&  “ ((-1) <= (count_pre - 1 )) ” 
  &&  “ ((count_pre - 1 ) < count_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Zlength (rows)) = count_pre) ” 
  &&  “ ((Zlength (lens)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows)) ) ” 
  &&  “ (Forall (Z.le (1)) lens ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ”
.

Definition concatenating_numbers_partial_solve_wit_1_aux := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (count_pre > 1)) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : ((Zlength (rows)) = count_pre)) (PreH9 : ((Zlength (lens)) = count_pre)) (PreH10 : (Forall (eq (number_width_pre)) (map (Zlength) (rows)) )) (PreH11 : (Forall (Z.le (1)) lens )) (PreH12 : (Forall (Z.ge (number_width_pre)) lens )) (PreH13 : (Forall (Z.le (1)) (map ((hd (0))) (rows)) )) (PreH14 : (Forall (Z.ge (9)) (map ((hd (0))) (rows)) )) (PreH15 : (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) )) (PreH16 : (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= count_pre) ” 
  &&  “ ((-1) <= (count_pre - 1 )) ” 
  &&  “ ((count_pre - 1 ) < count_pre) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Zlength (rows)) = count_pre) ” 
  &&  “ ((Zlength (lens)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows)) ) ” 
  &&  “ (Forall (Z.le (1)) lens ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (count_pre > 1) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ ((Zlength (rows)) = count_pre) ” 
  &&  “ ((Zlength (lens)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows)) ) ” 
  &&  “ (Forall (Z.le (1)) lens ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows) (lens)) ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
.

Definition concatenating_numbers_partial_solve_wit_1 := concatenating_numbers_partial_solve_wit_1_pure -> concatenating_numbers_partial_solve_wit_1_aux.

Definition concatenating_numbers_partial_solve_wit_2 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (output: (@list Z)) (rows1: (@list (@list Z))) (result_length: Z) (lens1: (@list Z)) (j: Z) (i: Z) (PreH1 : (0 <= (i * number_width_pre ))) (PreH2 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH3 : ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens))))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (1 <= (sum (lens)))) (PreH9 : ((sum (lens)) <= 200)) (PreH10 : (0 <= i)) (PreH11 : (i < count_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= (Znth (i) (lens1) (0)))) (PreH14 : (1 <= (Znth (i) (lens1) (0)))) (PreH15 : ((Znth (i) (lens1) (0)) <= number_width_pre)) (PreH16 : ((Zlength (rows1)) = count_pre)) (PreH17 : ((Zlength (lens1)) = count_pre)) (PreH18 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH19 : (Forall (Z.le (1)) lens1 )) (PreH20 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH21 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH22 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH24 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (PairedPermutation rows rows1 lens lens1 )) (PreH26 : (GreedySorted rows1 lens1 )) (PreH27 : ((sum (lens1)) = (sum (lens)))) (PreH28 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH29 : (result_length = (Zlength (output)))) (PreH30 : (0 <= result_length)) (PreH31 : (result_length <= (sum (lens)))) (PreH32 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (0 <= (i * number_width_pre )) ” 
  &&  “ (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens)))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < count_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (Znth (i) (lens1) (0))) ” 
  &&  “ (1 <= (Znth (i) (lens1) (0))) ” 
  &&  “ ((Znth (i) (lens1) (0)) <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (GreedySorted rows1 lens1 ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ (result_length <= (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (((lengths_pre + (i * sizeof(INT)))) # Int  |-> (Znth i lens1 0))
  **  (IntArray.missing_i lengths_pre i 0 count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
.

Definition concatenating_numbers_partial_solve_wit_3 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (output: (@list Z)) (rows1: (@list (@list Z))) (result_length: Z) (lens1: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < (Znth i lens1 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1) (0)))) (PreH15 : (1 <= (Znth (i) (lens1) (0)))) (PreH16 : ((Znth (i) (lens1) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (GreedySorted rows1 lens1 )) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (j < (Znth i lens1 0)) ” 
  &&  “ (0 <= (i * number_width_pre )) ” 
  &&  “ (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens)))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < count_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (Znth (i) (lens1) (0))) ” 
  &&  “ (1 <= (Znth (i) (lens1) (0))) ” 
  &&  “ ((Znth (i) (lens1) (0)) <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (GreedySorted rows1 lens1 ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ (result_length <= (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (((numbers_pre + (((i * number_width_pre ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((i * number_width_pre ) + j ) flat1 0))
  **  (IntArray.missing_i numbers_pre ((i * number_width_pre ) + j ) 0 (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
.

Definition concatenating_numbers_partial_solve_wit_4 := 
forall (result_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (lens: (@list Z)) (rows: (@list (@list Z))) (flat1: (@list Z)) (output: (@list Z)) (rows1: (@list (@list Z))) (result_length: Z) (lens1: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < (Znth i lens1 0))) (PreH2 : (0 <= (i * number_width_pre ))) (PreH3 : (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre ))) (PreH4 : ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens))))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (0 <= i)) (PreH12 : (i < count_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (Znth (i) (lens1) (0)))) (PreH15 : (1 <= (Znth (i) (lens1) (0)))) (PreH16 : ((Znth (i) (lens1) (0)) <= number_width_pre)) (PreH17 : ((Zlength (rows1)) = count_pre)) (PreH18 : ((Zlength (lens1)) = count_pre)) (PreH19 : (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) )) (PreH20 : (Forall (Z.le (1)) lens1 )) (PreH21 : (Forall (Z.ge (number_width_pre)) lens1 )) (PreH22 : (Forall (Z.le (1)) (map ((hd (0))) (rows1)) )) (PreH23 : (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) )) (PreH24 : (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) )) (PreH25 : (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) )) (PreH26 : (PairedPermutation rows rows1 lens lens1 )) (PreH27 : (GreedySorted rows1 lens1 )) (PreH28 : ((sum (lens1)) = (sum (lens)))) (PreH29 : (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j)))) (PreH30 : (result_length = (Zlength (output)))) (PreH31 : (0 <= result_length)) (PreH32 : (result_length <= (sum (lens)))) (PreH33 : (FlatRows flat1 rows1 count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (j < (Znth i lens1 0)) ” 
  &&  “ (0 <= (i * number_width_pre )) ” 
  &&  “ (((i * number_width_pre ) + number_width_pre ) <= (count_pre * number_width_pre )) ” 
  &&  “ ((j < (Znth (i) (lens1) (0))) -> (result_length < (sum (lens)))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < count_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (Znth (i) (lens1) (0))) ” 
  &&  “ (1 <= (Znth (i) (lens1) (0))) ” 
  &&  “ ((Znth (i) (lens1) (0)) <= number_width_pre) ” 
  &&  “ ((Zlength (rows1)) = count_pre) ” 
  &&  “ ((Zlength (lens1)) = count_pre) ” 
  &&  “ (Forall (eq (number_width_pre)) (map (Zlength) (rows1)) ) ” 
  &&  “ (Forall (Z.le (1)) lens1 ) ” 
  &&  “ (Forall (Z.ge (number_width_pre)) lens1 ) ” 
  &&  “ (Forall (Z.le (1)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (map ((hd (0))) (rows1)) ) ” 
  &&  “ (Forall (Z.le (0)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (Forall (Z.ge (9)) (concatenate_rows (rows1) (lens1)) ) ” 
  &&  “ (PairedPermutation rows rows1 lens lens1 ) ” 
  &&  “ (GreedySorted rows1 lens1 ) ” 
  &&  “ ((sum (lens1)) = (sum (lens))) ” 
  &&  “ (output = (ConcatenatedOutputPrefix (rows1) (lens1) (i) (j))) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ (result_length <= (sum (lens))) ” 
  &&  “ (FlatRows flat1 rows1 count_pre number_width_pre ) ”
  &&  (((result_pre + (result_length * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat1 )
  **  (IntArray.full lengths_pre count_pre lens1 )
  **  (IntArray.seg result_pre 0 result_length output )
.

Module Type VC_Correct.

Include array2_Strategy_Correct.
Include int_array_Strategy_Correct.

Axiom proof_of_quicksort_numbers_safety_wit_1 : quicksort_numbers_safety_wit_1.
Axiom proof_of_quicksort_numbers_safety_wit_2 : quicksort_numbers_safety_wit_2.
Axiom proof_of_quicksort_numbers_safety_wit_3 : quicksort_numbers_safety_wit_3.
Axiom proof_of_quicksort_numbers_safety_wit_4 : quicksort_numbers_safety_wit_4.
Axiom proof_of_quicksort_numbers_safety_wit_5 : quicksort_numbers_safety_wit_5.
Axiom proof_of_quicksort_numbers_safety_wit_6 : quicksort_numbers_safety_wit_6.
Axiom proof_of_quicksort_numbers_safety_wit_7 : quicksort_numbers_safety_wit_7.
Axiom proof_of_quicksort_numbers_safety_wit_8 : quicksort_numbers_safety_wit_8.
Axiom proof_of_quicksort_numbers_safety_wit_9 : quicksort_numbers_safety_wit_9.
Axiom proof_of_quicksort_numbers_safety_wit_10 : quicksort_numbers_safety_wit_10.
Axiom proof_of_quicksort_numbers_safety_wit_11 : quicksort_numbers_safety_wit_11.
Axiom proof_of_quicksort_numbers_safety_wit_12 : quicksort_numbers_safety_wit_12.
Axiom proof_of_quicksort_numbers_safety_wit_13 : quicksort_numbers_safety_wit_13.
Axiom proof_of_quicksort_numbers_safety_wit_14 : quicksort_numbers_safety_wit_14.
Axiom proof_of_quicksort_numbers_safety_wit_15 : quicksort_numbers_safety_wit_15.
Axiom proof_of_quicksort_numbers_safety_wit_16 : quicksort_numbers_safety_wit_16.
Axiom proof_of_quicksort_numbers_safety_wit_17 : quicksort_numbers_safety_wit_17.
Axiom proof_of_quicksort_numbers_safety_wit_18 : quicksort_numbers_safety_wit_18.
Axiom proof_of_quicksort_numbers_safety_wit_19 : quicksort_numbers_safety_wit_19.
Axiom proof_of_quicksort_numbers_safety_wit_20 : quicksort_numbers_safety_wit_20.
Axiom proof_of_quicksort_numbers_safety_wit_21 : quicksort_numbers_safety_wit_21.
Axiom proof_of_quicksort_numbers_safety_wit_22 : quicksort_numbers_safety_wit_22.
Axiom proof_of_quicksort_numbers_safety_wit_23 : quicksort_numbers_safety_wit_23.
Axiom proof_of_quicksort_numbers_safety_wit_24 : quicksort_numbers_safety_wit_24.
Axiom proof_of_quicksort_numbers_safety_wit_25 : quicksort_numbers_safety_wit_25.
Axiom proof_of_quicksort_numbers_safety_wit_26 : quicksort_numbers_safety_wit_26.
Axiom proof_of_quicksort_numbers_safety_wit_27 : quicksort_numbers_safety_wit_27.
Axiom proof_of_quicksort_numbers_safety_wit_28 : quicksort_numbers_safety_wit_28.
Axiom proof_of_quicksort_numbers_safety_wit_29 : quicksort_numbers_safety_wit_29.
Axiom proof_of_quicksort_numbers_safety_wit_30 : quicksort_numbers_safety_wit_30.
Axiom proof_of_quicksort_numbers_safety_wit_31 : quicksort_numbers_safety_wit_31.
Axiom proof_of_quicksort_numbers_safety_wit_32 : quicksort_numbers_safety_wit_32.
Axiom proof_of_quicksort_numbers_safety_wit_33 : quicksort_numbers_safety_wit_33.
Axiom proof_of_quicksort_numbers_safety_wit_34 : quicksort_numbers_safety_wit_34.
Axiom proof_of_quicksort_numbers_safety_wit_35 : quicksort_numbers_safety_wit_35.
Axiom proof_of_quicksort_numbers_safety_wit_36 : quicksort_numbers_safety_wit_36.
Axiom proof_of_quicksort_numbers_safety_wit_37 : quicksort_numbers_safety_wit_37.
Axiom proof_of_quicksort_numbers_safety_wit_38 : quicksort_numbers_safety_wit_38.
Axiom proof_of_quicksort_numbers_safety_wit_39 : quicksort_numbers_safety_wit_39.
Axiom proof_of_quicksort_numbers_safety_wit_40 : quicksort_numbers_safety_wit_40.
Axiom proof_of_quicksort_numbers_safety_wit_41 : quicksort_numbers_safety_wit_41.
Axiom proof_of_quicksort_numbers_safety_wit_42 : quicksort_numbers_safety_wit_42.
Axiom proof_of_quicksort_numbers_safety_wit_43 : quicksort_numbers_safety_wit_43.
Axiom proof_of_quicksort_numbers_safety_wit_44 : quicksort_numbers_safety_wit_44.
Axiom proof_of_quicksort_numbers_safety_wit_45 : quicksort_numbers_safety_wit_45.
Axiom proof_of_quicksort_numbers_safety_wit_46 : quicksort_numbers_safety_wit_46.
Axiom proof_of_quicksort_numbers_safety_wit_47 : quicksort_numbers_safety_wit_47.
Axiom proof_of_quicksort_numbers_safety_wit_48 : quicksort_numbers_safety_wit_48.
Axiom proof_of_quicksort_numbers_safety_wit_49 : quicksort_numbers_safety_wit_49.
Axiom proof_of_quicksort_numbers_safety_wit_50 : quicksort_numbers_safety_wit_50.
Axiom proof_of_quicksort_numbers_safety_wit_51 : quicksort_numbers_safety_wit_51.
Axiom proof_of_quicksort_numbers_safety_wit_52 : quicksort_numbers_safety_wit_52.
Axiom proof_of_quicksort_numbers_entail_wit_1 : quicksort_numbers_entail_wit_1.
Axiom proof_of_quicksort_numbers_entail_wit_2 : quicksort_numbers_entail_wit_2.
Axiom proof_of_quicksort_numbers_entail_wit_3_1 : quicksort_numbers_entail_wit_3_1.
Axiom proof_of_quicksort_numbers_entail_wit_3_2 : quicksort_numbers_entail_wit_3_2.
Axiom proof_of_quicksort_numbers_entail_wit_4_1 : quicksort_numbers_entail_wit_4_1.
Axiom proof_of_quicksort_numbers_entail_wit_4_2 : quicksort_numbers_entail_wit_4_2.
Axiom proof_of_quicksort_numbers_entail_wit_5 : quicksort_numbers_entail_wit_5.
Axiom proof_of_quicksort_numbers_entail_wit_6_1 : quicksort_numbers_entail_wit_6_1.
Axiom proof_of_quicksort_numbers_entail_wit_6_2 : quicksort_numbers_entail_wit_6_2.
Axiom proof_of_quicksort_numbers_entail_wit_7 : quicksort_numbers_entail_wit_7.
Axiom proof_of_quicksort_numbers_entail_wit_8 : quicksort_numbers_entail_wit_8.
Axiom proof_of_quicksort_numbers_entail_wit_9_1 : quicksort_numbers_entail_wit_9_1.
Axiom proof_of_quicksort_numbers_entail_wit_9_2 : quicksort_numbers_entail_wit_9_2.
Axiom proof_of_quicksort_numbers_entail_wit_10 : quicksort_numbers_entail_wit_10.
Axiom proof_of_quicksort_numbers_entail_wit_11 : quicksort_numbers_entail_wit_11.
Axiom proof_of_quicksort_numbers_entail_wit_12 : quicksort_numbers_entail_wit_12.
Axiom proof_of_quicksort_numbers_entail_wit_13 : quicksort_numbers_entail_wit_13.
Axiom proof_of_quicksort_numbers_return_wit_1 : quicksort_numbers_return_wit_1.
Axiom proof_of_quicksort_numbers_return_wit_2 : quicksort_numbers_return_wit_2.
Axiom proof_of_quicksort_numbers_return_wit_3 : quicksort_numbers_return_wit_3.
Axiom proof_of_quicksort_numbers_return_wit_4 : quicksort_numbers_return_wit_4.
Axiom proof_of_quicksort_numbers_partial_solve_wit_1 : quicksort_numbers_partial_solve_wit_1.
Axiom proof_of_quicksort_numbers_partial_solve_wit_2 : quicksort_numbers_partial_solve_wit_2.
Axiom proof_of_quicksort_numbers_partial_solve_wit_3 : quicksort_numbers_partial_solve_wit_3.
Axiom proof_of_quicksort_numbers_partial_solve_wit_4 : quicksort_numbers_partial_solve_wit_4.
Axiom proof_of_quicksort_numbers_partial_solve_wit_5 : quicksort_numbers_partial_solve_wit_5.
Axiom proof_of_quicksort_numbers_partial_solve_wit_6 : quicksort_numbers_partial_solve_wit_6.
Axiom proof_of_quicksort_numbers_partial_solve_wit_7 : quicksort_numbers_partial_solve_wit_7.
Axiom proof_of_quicksort_numbers_partial_solve_wit_8 : quicksort_numbers_partial_solve_wit_8.
Axiom proof_of_quicksort_numbers_partial_solve_wit_9 : quicksort_numbers_partial_solve_wit_9.
Axiom proof_of_quicksort_numbers_partial_solve_wit_10 : quicksort_numbers_partial_solve_wit_10.
Axiom proof_of_quicksort_numbers_partial_solve_wit_11 : quicksort_numbers_partial_solve_wit_11.
Axiom proof_of_quicksort_numbers_partial_solve_wit_12 : quicksort_numbers_partial_solve_wit_12.
Axiom proof_of_quicksort_numbers_partial_solve_wit_13 : quicksort_numbers_partial_solve_wit_13.
Axiom proof_of_quicksort_numbers_partial_solve_wit_14 : quicksort_numbers_partial_solve_wit_14.
Axiom proof_of_quicksort_numbers_partial_solve_wit_15 : quicksort_numbers_partial_solve_wit_15.
Axiom proof_of_quicksort_numbers_partial_solve_wit_16 : quicksort_numbers_partial_solve_wit_16.
Axiom proof_of_quicksort_numbers_partial_solve_wit_17 : quicksort_numbers_partial_solve_wit_17.
Axiom proof_of_quicksort_numbers_partial_solve_wit_18 : quicksort_numbers_partial_solve_wit_18.
Axiom proof_of_quicksort_numbers_partial_solve_wit_19 : quicksort_numbers_partial_solve_wit_19.
Axiom proof_of_quicksort_numbers_partial_solve_wit_20 : quicksort_numbers_partial_solve_wit_20.
Axiom proof_of_quicksort_numbers_partial_solve_wit_21 : quicksort_numbers_partial_solve_wit_21.
Axiom proof_of_quicksort_numbers_partial_solve_wit_22_pure : quicksort_numbers_partial_solve_wit_22_pure.
Axiom proof_of_quicksort_numbers_partial_solve_wit_22 : quicksort_numbers_partial_solve_wit_22.
Axiom proof_of_quicksort_numbers_partial_solve_wit_23_pure : quicksort_numbers_partial_solve_wit_23_pure.
Axiom proof_of_quicksort_numbers_partial_solve_wit_23 : quicksort_numbers_partial_solve_wit_23.
Axiom proof_of_quicksort_numbers_partial_solve_wit_24_pure : quicksort_numbers_partial_solve_wit_24_pure.
Axiom proof_of_quicksort_numbers_partial_solve_wit_24 : quicksort_numbers_partial_solve_wit_24.
Axiom proof_of_concatenating_numbers_safety_wit_1 : concatenating_numbers_safety_wit_1.
Axiom proof_of_concatenating_numbers_safety_wit_2 : concatenating_numbers_safety_wit_2.
Axiom proof_of_concatenating_numbers_safety_wit_3 : concatenating_numbers_safety_wit_3.
Axiom proof_of_concatenating_numbers_safety_wit_4 : concatenating_numbers_safety_wit_4.
Axiom proof_of_concatenating_numbers_safety_wit_5 : concatenating_numbers_safety_wit_5.
Axiom proof_of_concatenating_numbers_safety_wit_6 : concatenating_numbers_safety_wit_6.
Axiom proof_of_concatenating_numbers_safety_wit_7 : concatenating_numbers_safety_wit_7.
Axiom proof_of_concatenating_numbers_safety_wit_8 : concatenating_numbers_safety_wit_8.
Axiom proof_of_concatenating_numbers_safety_wit_9 : concatenating_numbers_safety_wit_9.
Axiom proof_of_concatenating_numbers_safety_wit_10 : concatenating_numbers_safety_wit_10.
Axiom proof_of_concatenating_numbers_safety_wit_11 : concatenating_numbers_safety_wit_11.
Axiom proof_of_concatenating_numbers_safety_wit_12 : concatenating_numbers_safety_wit_12.
Axiom proof_of_concatenating_numbers_safety_wit_13 : concatenating_numbers_safety_wit_13.
Axiom proof_of_concatenating_numbers_entail_wit_1 : concatenating_numbers_entail_wit_1.
Axiom proof_of_concatenating_numbers_entail_wit_2_1 : concatenating_numbers_entail_wit_2_1.
Axiom proof_of_concatenating_numbers_entail_wit_2_2 : concatenating_numbers_entail_wit_2_2.
Axiom proof_of_concatenating_numbers_entail_wit_3 : concatenating_numbers_entail_wit_3.
Axiom proof_of_concatenating_numbers_entail_wit_4 : concatenating_numbers_entail_wit_4.
Axiom proof_of_concatenating_numbers_entail_wit_5 : concatenating_numbers_entail_wit_5.
Axiom proof_of_concatenating_numbers_return_wit_1 : concatenating_numbers_return_wit_1.
Axiom proof_of_concatenating_numbers_partial_solve_wit_1_pure : concatenating_numbers_partial_solve_wit_1_pure.
Axiom proof_of_concatenating_numbers_partial_solve_wit_1 : concatenating_numbers_partial_solve_wit_1.
Axiom proof_of_concatenating_numbers_partial_solve_wit_2 : concatenating_numbers_partial_solve_wit_2.
Axiom proof_of_concatenating_numbers_partial_solve_wit_3 : concatenating_numbers_partial_solve_wit_3.
Axiom proof_of_concatenating_numbers_partial_solve_wit_4 : concatenating_numbers_partial_solve_wit_4.

End VC_Correct.
