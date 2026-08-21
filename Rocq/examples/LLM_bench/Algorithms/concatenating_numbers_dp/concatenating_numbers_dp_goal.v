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
Require Import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_lib.
Local Open Scope sac.

(*----- Function compare_concatenated_order -----*)

Definition compare_concatenated_order_safety_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  ((( &( "total_length" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_length" ) )) # Int  |-> (Znth right_pre lens 0))
  **  ((( &( "left_length" ) )) # Int  |-> (Znth left_pre lens 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
|--
  “ (((Znth left_pre lens 0) + (Znth right_pre lens 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth left_pre lens 0) + (Znth right_pre lens 0) )) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  ((( &( "total_length" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_length" ) )) # Int  |-> (Znth right_pre lens 0))
  **  ((( &( "left_length" ) )) # Int  |-> (Znth left_pre lens 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
|--
  “ (((Znth left_pre lens 0) + (Znth right_pre lens 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth left_pre lens 0) + (Znth right_pre lens 0) )) ”
).

Definition compare_concatenated_order_safety_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  ((( &( "total_length" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_length" ) )) # Int  |-> (Znth right_pre lens 0))
  **  ((( &( "left_length" ) )) # Int  |-> (Znth left_pre lens 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
|--
  “ (((Znth left_pre lens 0) + (Znth right_pre lens 0) ) <= INT_MAX) ”
.

Definition compare_concatenated_order_safety_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  ((( &( "total_length" ) )) # Int  |->_)
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_length" ) )) # Int  |-> (Znth right_pre lens 0))
  **  ((( &( "left_length" ) )) # Int  |-> (Znth left_pre lens 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
|--
  “ ((INT_MIN) <= ((Znth left_pre lens 0) + (Znth right_pre lens 0) )) ”
.

Definition compare_concatenated_order_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "total_length" ) )) # Int  |-> ((Znth left_pre lens 0) + (Znth right_pre lens 0) ))
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_length" ) )) # Int  |-> (Znth right_pre lens 0))
  **  ((( &( "left_length" ) )) # Int  |-> (Znth left_pre lens 0))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition compare_concatenated_order_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= ((left_pre * number_width_pre ) + position ))) (PreH2 : (((left_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (total_length >= INT_MIN)) (PreH11 : (right_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position < left_length)) (PreH16 : (position < total_length)) (PreH17 : (1 <= count)) (PreH18 : (count <= 20)) (PreH19 : (1 <= number_width_pre)) (PreH20 : (number_width_pre <= 10)) (PreH21 : (0 <= left_pre)) (PreH22 : (left_pre < count)) (PreH23 : (0 <= right_pre)) (PreH24 : (right_pre < count)) (PreH25 : (1 <= left_length)) (PreH26 : (left_length <= number_width_pre)) (PreH27 : (1 <= right_length)) (PreH28 : (right_length <= number_width_pre)) (PreH29 : (total_length = (left_length + right_length ))) (PreH30 : (2 <= total_length)) (PreH31 : (total_length <= (2 * number_width_pre ))) (PreH32 : (0 <= position)) (PreH33 : (position <= total_length)) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (((left_pre * number_width_pre ) + position ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left_pre * number_width_pre ) + position )) ”
.

Definition compare_concatenated_order_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= ((left_pre * number_width_pre ) + position ))) (PreH2 : (((left_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (total_length >= INT_MIN)) (PreH11 : (right_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position < left_length)) (PreH16 : (position < total_length)) (PreH17 : (1 <= count)) (PreH18 : (count <= 20)) (PreH19 : (1 <= number_width_pre)) (PreH20 : (number_width_pre <= 10)) (PreH21 : (0 <= left_pre)) (PreH22 : (left_pre < count)) (PreH23 : (0 <= right_pre)) (PreH24 : (right_pre < count)) (PreH25 : (1 <= left_length)) (PreH26 : (left_length <= number_width_pre)) (PreH27 : (1 <= right_length)) (PreH28 : (right_length <= number_width_pre)) (PreH29 : (total_length = (left_length + right_length ))) (PreH30 : (2 <= total_length)) (PreH31 : (total_length <= (2 * number_width_pre ))) (PreH32 : (0 <= position)) (PreH33 : (position <= total_length)) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ ((left_pre * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_pre * number_width_pre )) ”
.

Definition compare_concatenated_order_safety_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= (((right_pre * number_width_pre ) + position ) - left_length ))) (PreH2 : ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - left_length ))) (PreH4 : ((position - left_length ) < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (right_pre <= INT_MAX)) (PreH8 : (left_pre <= INT_MAX)) (PreH9 : (total_length >= INT_MIN)) (PreH10 : (right_length >= INT_MIN)) (PreH11 : (right_pre >= INT_MIN)) (PreH12 : (left_pre >= INT_MIN)) (PreH13 : (position >= left_length)) (PreH14 : (position < total_length)) (PreH15 : (1 <= count)) (PreH16 : (count <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre < count)) (PreH21 : (0 <= right_pre)) (PreH22 : (right_pre < count)) (PreH23 : (1 <= left_length)) (PreH24 : (left_length <= number_width_pre)) (PreH25 : (1 <= right_length)) (PreH26 : (right_length <= number_width_pre)) (PreH27 : (total_length = (left_length + right_length ))) (PreH28 : (2 <= total_length)) (PreH29 : (total_length <= (2 * number_width_pre ))) (PreH30 : (0 <= position)) (PreH31 : (position <= total_length)) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ ((((right_pre * number_width_pre ) + position ) - left_length ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((right_pre * number_width_pre ) + position ) - left_length )) ”
.

Definition compare_concatenated_order_safety_wit_6 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= (((right_pre * number_width_pre ) + position ) - left_length ))) (PreH2 : ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - left_length ))) (PreH4 : ((position - left_length ) < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (right_pre <= INT_MAX)) (PreH8 : (left_pre <= INT_MAX)) (PreH9 : (total_length >= INT_MIN)) (PreH10 : (right_length >= INT_MIN)) (PreH11 : (right_pre >= INT_MIN)) (PreH12 : (left_pre >= INT_MIN)) (PreH13 : (position >= left_length)) (PreH14 : (position < total_length)) (PreH15 : (1 <= count)) (PreH16 : (count <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre < count)) (PreH21 : (0 <= right_pre)) (PreH22 : (right_pre < count)) (PreH23 : (1 <= left_length)) (PreH24 : (left_length <= number_width_pre)) (PreH25 : (1 <= right_length)) (PreH26 : (right_length <= number_width_pre)) (PreH27 : (total_length = (left_length + right_length ))) (PreH28 : (2 <= total_length)) (PreH29 : (total_length <= (2 * number_width_pre ))) (PreH30 : (0 <= position)) (PreH31 : (position <= total_length)) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (((right_pre * number_width_pre ) + position ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right_pre * number_width_pre ) + position )) ”
.

Definition compare_concatenated_order_safety_wit_7 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= (((right_pre * number_width_pre ) + position ) - left_length ))) (PreH2 : ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - left_length ))) (PreH4 : ((position - left_length ) < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (right_pre <= INT_MAX)) (PreH8 : (left_pre <= INT_MAX)) (PreH9 : (total_length >= INT_MIN)) (PreH10 : (right_length >= INT_MIN)) (PreH11 : (right_pre >= INT_MIN)) (PreH12 : (left_pre >= INT_MIN)) (PreH13 : (position >= left_length)) (PreH14 : (position < total_length)) (PreH15 : (1 <= count)) (PreH16 : (count <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre < count)) (PreH21 : (0 <= right_pre)) (PreH22 : (right_pre < count)) (PreH23 : (1 <= left_length)) (PreH24 : (left_length <= number_width_pre)) (PreH25 : (1 <= right_length)) (PreH26 : (right_length <= number_width_pre)) (PreH27 : (total_length = (left_length + right_length ))) (PreH28 : (2 <= total_length)) (PreH29 : (total_length <= (2 * number_width_pre ))) (PreH30 : (0 <= position)) (PreH31 : (position <= total_length)) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ ((right_pre * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right_pre * number_width_pre )) ”
.

Definition compare_concatenated_order_safety_wit_8 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= ((right_pre * number_width_pre ) + position ))) (PreH2 : (((right_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (right_length <= INT_MAX)) (PreH8 : (left_length <= INT_MAX)) (PreH9 : (right_pre <= INT_MAX)) (PreH10 : (left_pre <= INT_MAX)) (PreH11 : (left_then_right >= INT_MIN)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (right_length >= INT_MIN)) (PreH14 : (left_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position < right_length)) (PreH18 : (1 <= count)) (PreH19 : (count <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : (0 <= left_pre)) (PreH23 : (left_pre < count)) (PreH24 : (0 <= right_pre)) (PreH25 : (right_pre < count)) (PreH26 : (1 <= left_length)) (PreH27 : (left_length <= number_width_pre)) (PreH28 : (1 <= right_length)) (PreH29 : (right_length <= number_width_pre)) (PreH30 : (total_length = (left_length + right_length ))) (PreH31 : (0 <= position)) (PreH32 : (position < total_length)) (PreH33 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
|--
  “ (((right_pre * number_width_pre ) + position ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right_pre * number_width_pre ) + position )) ”
.

Definition compare_concatenated_order_safety_wit_9 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= ((right_pre * number_width_pre ) + position ))) (PreH2 : (((right_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (right_length <= INT_MAX)) (PreH8 : (left_length <= INT_MAX)) (PreH9 : (right_pre <= INT_MAX)) (PreH10 : (left_pre <= INT_MAX)) (PreH11 : (left_then_right >= INT_MIN)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (right_length >= INT_MIN)) (PreH14 : (left_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position < right_length)) (PreH18 : (1 <= count)) (PreH19 : (count <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : (0 <= left_pre)) (PreH23 : (left_pre < count)) (PreH24 : (0 <= right_pre)) (PreH25 : (right_pre < count)) (PreH26 : (1 <= left_length)) (PreH27 : (left_length <= number_width_pre)) (PreH28 : (1 <= right_length)) (PreH29 : (right_length <= number_width_pre)) (PreH30 : (total_length = (left_length + right_length ))) (PreH31 : (0 <= position)) (PreH32 : (position < total_length)) (PreH33 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
|--
  “ ((right_pre * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right_pre * number_width_pre )) ”
.

Definition compare_concatenated_order_safety_wit_10 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= (((left_pre * number_width_pre ) + position ) - right_length ))) (PreH2 : ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - right_length ))) (PreH4 : ((position - right_length ) < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (left_then_right >= INT_MIN)) (PreH11 : (total_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position >= right_length)) (PreH16 : (1 <= count)) (PreH17 : (count <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre < count)) (PreH22 : (0 <= right_pre)) (PreH23 : (right_pre < count)) (PreH24 : (1 <= left_length)) (PreH25 : (left_length <= number_width_pre)) (PreH26 : (1 <= right_length)) (PreH27 : (right_length <= number_width_pre)) (PreH28 : (total_length = (left_length + right_length ))) (PreH29 : (0 <= position)) (PreH30 : (position < total_length)) (PreH31 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
|--
  “ ((((left_pre * number_width_pre ) + position ) - right_length ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((left_pre * number_width_pre ) + position ) - right_length )) ”
.

Definition compare_concatenated_order_safety_wit_11 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= (((left_pre * number_width_pre ) + position ) - right_length ))) (PreH2 : ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - right_length ))) (PreH4 : ((position - right_length ) < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (left_then_right >= INT_MIN)) (PreH11 : (total_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position >= right_length)) (PreH16 : (1 <= count)) (PreH17 : (count <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre < count)) (PreH22 : (0 <= right_pre)) (PreH23 : (right_pre < count)) (PreH24 : (1 <= left_length)) (PreH25 : (left_length <= number_width_pre)) (PreH26 : (1 <= right_length)) (PreH27 : (right_length <= number_width_pre)) (PreH28 : (total_length = (left_length + right_length ))) (PreH29 : (0 <= position)) (PreH30 : (position < total_length)) (PreH31 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
|--
  “ (((left_pre * number_width_pre ) + position ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left_pre * number_width_pre ) + position )) ”
.

Definition compare_concatenated_order_safety_wit_12 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= (((left_pre * number_width_pre ) + position ) - right_length ))) (PreH2 : ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - right_length ))) (PreH4 : ((position - right_length ) < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (left_then_right >= INT_MIN)) (PreH11 : (total_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position >= right_length)) (PreH16 : (1 <= count)) (PreH17 : (count <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre < count)) (PreH22 : (0 <= right_pre)) (PreH23 : (right_pre < count)) (PreH24 : (1 <= left_length)) (PreH25 : (left_length <= number_width_pre)) (PreH26 : (1 <= right_length)) (PreH27 : (right_length <= number_width_pre)) (PreH28 : (total_length = (left_length + right_length ))) (PreH29 : (0 <= position)) (PreH30 : (position < total_length)) (PreH31 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
|--
  “ ((left_pre * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_pre * number_width_pre )) ”
.

Definition compare_concatenated_order_safety_wit_13 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right > right_then_left)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (0 <= position)) (PreH16 : (position < total_length)) (PreH17 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH18 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (RowsWellFormed rows lens count number_width_pre )) (PreH20 : (FlatRows flat rows count number_width_pre )) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  ((( &( "right_then_left" ) )) # Int  |-> right_then_left)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition compare_concatenated_order_safety_wit_14 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right < right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (0 <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  ((( &( "right_then_left" ) )) # Int  |-> right_then_left)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition compare_concatenated_order_safety_wit_15 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right < right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (0 <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  ((( &( "right_then_left" ) )) # Int  |-> right_then_left)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition compare_concatenated_order_safety_wit_16 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right >= right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (0 <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ ((position + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (position + 1 )) ”
.

Definition compare_concatenated_order_safety_wit_17 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (position >= total_length)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (2 <= total_length)) (PreH16 : (total_length <= (2 * number_width_pre ))) (PreH17 : (0 <= position)) (PreH18 : (position <= total_length)) (PreH19 : (RowsWellFormed rows lens count number_width_pre )) (PreH20 : (FlatRows flat rows count number_width_pre )) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition compare_concatenated_order_entail_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  (IntArray.full lengths_pre count lens )
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
|--
  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= (Znth left_pre lens 0)) ” 
  &&  “ ((Znth left_pre lens 0) <= number_width_pre) ” 
  &&  “ (1 <= (Znth right_pre lens 0)) ” 
  &&  “ ((Znth right_pre lens 0) <= number_width_pre) ” 
  &&  “ (((Znth left_pre lens 0) + (Znth right_pre lens 0) ) = ((Znth left_pre lens 0) + (Znth right_pre lens 0) )) ” 
  &&  “ (2 <= ((Znth left_pre lens 0) + (Znth right_pre lens 0) )) ” 
  &&  “ (((Znth left_pre lens 0) + (Znth right_pre lens 0) ) <= (2 * number_width_pre )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((Znth left_pre lens 0) + (Znth right_pre lens 0) )) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre (Znth left_pre lens 0) (Znth right_pre lens 0) 0 ) ”
  &&  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  TT && emp 
|--
  “ (ConcatCompareLoopState rows lens left_pre right_pre (Znth left_pre lens 0) (Znth right_pre lens 0) 0 ) ” 
  &&  “ (0 <= ((Znth left_pre lens 0) + (Znth right_pre lens 0) )) ” 
  &&  “ (((Znth left_pre lens 0) + (Znth right_pre lens 0) ) <= (2 * number_width_pre )) ” 
  &&  “ (2 <= ((Znth left_pre lens 0) + (Znth right_pre lens 0) )) ” 
  &&  “ ((Znth right_pre lens 0) <= number_width_pre) ” 
  &&  “ (1 <= (Znth right_pre lens 0)) ” 
  &&  “ ((Znth left_pre lens 0) <= number_width_pre) ” 
  &&  “ (1 <= (Znth left_pre lens 0)) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  (ConcatCompareLoopState rows lens left_pre right_pre (Znth left_pre lens 0) (Znth right_pre lens 0) 0 )
.

Definition compare_concatenated_order_entail_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  (0 <= ((Znth left_pre lens 0) + (Znth right_pre lens 0) ))
.

Definition compare_concatenated_order_entail_wit_1_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  (((Znth left_pre lens 0) + (Znth right_pre lens 0) ) <= (2 * number_width_pre ))
.

Definition compare_concatenated_order_entail_wit_1_split_goal_4 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  (2 <= ((Znth left_pre lens 0) + (Znth right_pre lens 0) ))
.

Definition compare_concatenated_order_entail_wit_1_split_goal_5 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  ((Znth right_pre lens 0) <= number_width_pre)
.

Definition compare_concatenated_order_entail_wit_1_split_goal_6 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  (1 <= (Znth right_pre lens 0))
.

Definition compare_concatenated_order_entail_wit_1_split_goal_7 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  ((Znth left_pre lens 0) <= number_width_pre)
.

Definition compare_concatenated_order_entail_wit_1_split_goal_8 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  (1 <= (Znth left_pre lens 0))
.

Definition compare_concatenated_order_entail_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (position < left_length)) (PreH2 : (position < total_length)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (2 <= total_length)) (PreH17 : (total_length <= (2 * number_width_pre ))) (PreH18 : (0 <= position)) (PreH19 : (position <= total_length)) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (0 <= position) ” 
  &&  “ (position < number_width_pre) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (right_length <= INT_MAX) ” 
  &&  “ (left_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (right_length >= INT_MIN) ” 
  &&  “ (left_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position < left_length) ” 
  &&  “ (position < total_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (2 <= total_length) ” 
  &&  “ (total_length <= (2 * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= total_length) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
.

Definition compare_concatenated_order_entail_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= position)) (PreH2 : (position < number_width_pre)) (PreH3 : (total_length <= INT_MAX)) (PreH4 : (right_length <= INT_MAX)) (PreH5 : (left_length <= INT_MAX)) (PreH6 : (right_pre <= INT_MAX)) (PreH7 : (left_pre <= INT_MAX)) (PreH8 : (total_length >= INT_MIN)) (PreH9 : (right_length >= INT_MIN)) (PreH10 : (left_length >= INT_MIN)) (PreH11 : (right_pre >= INT_MIN)) (PreH12 : (left_pre >= INT_MIN)) (PreH13 : (position < left_length)) (PreH14 : (position < total_length)) (PreH15 : (1 <= count)) (PreH16 : (count <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre < count)) (PreH21 : (0 <= right_pre)) (PreH22 : (right_pre < count)) (PreH23 : (1 <= left_length)) (PreH24 : (left_length <= number_width_pre)) (PreH25 : (1 <= right_length)) (PreH26 : (right_length <= number_width_pre)) (PreH27 : (total_length = (left_length + right_length ))) (PreH28 : (2 <= total_length)) (PreH29 : (total_length <= (2 * number_width_pre ))) (PreH30 : (0 <= position)) (PreH31 : (position <= total_length)) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (0 <= ((left_pre * number_width_pre ) + position )) ” 
  &&  “ (((left_pre * number_width_pre ) + position ) < (count * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < number_width_pre) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (right_length <= INT_MAX) ” 
  &&  “ (left_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (right_length >= INT_MIN) ” 
  &&  “ (left_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position < left_length) ” 
  &&  “ (position < total_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (2 <= total_length) ” 
  &&  “ (total_length <= (2 * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= total_length) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : (0 <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (right_length <= INT_MAX)) (PreH9 : (left_length <= INT_MAX)) (PreH10 : (right_pre <= INT_MAX)) (PreH11 : (left_pre <= INT_MAX)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (right_length >= INT_MIN)) (PreH14 : (left_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position < left_length)) (PreH18 : (position < total_length)) (PreH19 : (1 <= count)) (PreH20 : (count <= 20)) (PreH21 : (1 <= number_width_pre)) (PreH22 : (number_width_pre <= 10)) (PreH23 : (0 <= left_pre)) (PreH24 : (left_pre < count)) (PreH25 : (0 <= right_pre)) (PreH26 : (right_pre < count)) (PreH27 : (1 <= left_length)) (PreH28 : (left_length <= number_width_pre)) (PreH29 : (1 <= right_length)) (PreH30 : (right_length <= number_width_pre)) (PreH31 : (total_length = (left_length + right_length ))) (PreH32 : (2 <= total_length)) (PreH33 : (total_length <= (2 * number_width_pre ))) (PreH34 : (0 <= position)) (PreH35 : (position <= total_length)) (PreH36 : (RowsWellFormed rows lens count number_width_pre )) (PreH37 : (FlatRows flat rows count number_width_pre )) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ (((left_pre * number_width_pre ) + position ) < (count * number_width_pre )) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : (0 <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (total_length <= INT_MAX)) (PreH8 : (right_length <= INT_MAX)) (PreH9 : (left_length <= INT_MAX)) (PreH10 : (right_pre <= INT_MAX)) (PreH11 : (left_pre <= INT_MAX)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (right_length >= INT_MIN)) (PreH14 : (left_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position < left_length)) (PreH18 : (position < total_length)) (PreH19 : (1 <= count)) (PreH20 : (count <= 20)) (PreH21 : (1 <= number_width_pre)) (PreH22 : (number_width_pre <= 10)) (PreH23 : (0 <= left_pre)) (PreH24 : (left_pre < count)) (PreH25 : (0 <= right_pre)) (PreH26 : (right_pre < count)) (PreH27 : (1 <= left_length)) (PreH28 : (left_length <= number_width_pre)) (PreH29 : (1 <= right_length)) (PreH30 : (right_length <= number_width_pre)) (PreH31 : (total_length = (left_length + right_length ))) (PreH32 : (2 <= total_length)) (PreH33 : (total_length <= (2 * number_width_pre ))) (PreH34 : (0 <= position)) (PreH35 : (position <= total_length)) (PreH36 : (RowsWellFormed rows lens count number_width_pre )) (PreH37 : (FlatRows flat rows count number_width_pre )) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (((left_pre * number_width_pre ) + position ) < (count * number_width_pre ))
.

Definition compare_concatenated_order_entail_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (position >= left_length)) (PreH2 : (position < total_length)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (2 <= total_length)) (PreH17 : (total_length <= (2 * number_width_pre ))) (PreH18 : (0 <= position)) (PreH19 : (position <= total_length)) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (0 <= (position - left_length )) ” 
  &&  “ ((position - left_length ) < number_width_pre) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (right_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (right_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position >= left_length) ” 
  &&  “ (position < total_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (2 <= total_length) ” 
  &&  “ (total_length <= (2 * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= total_length) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
.

Definition compare_concatenated_order_entail_wit_5 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= (position - left_length ))) (PreH2 : ((position - left_length ) < number_width_pre)) (PreH3 : (total_length <= INT_MAX)) (PreH4 : (right_length <= INT_MAX)) (PreH5 : (right_pre <= INT_MAX)) (PreH6 : (left_pre <= INT_MAX)) (PreH7 : (total_length >= INT_MIN)) (PreH8 : (right_length >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (position >= left_length)) (PreH12 : (position < total_length)) (PreH13 : (1 <= count)) (PreH14 : (count <= 20)) (PreH15 : (1 <= number_width_pre)) (PreH16 : (number_width_pre <= 10)) (PreH17 : (0 <= left_pre)) (PreH18 : (left_pre < count)) (PreH19 : (0 <= right_pre)) (PreH20 : (right_pre < count)) (PreH21 : (1 <= left_length)) (PreH22 : (left_length <= number_width_pre)) (PreH23 : (1 <= right_length)) (PreH24 : (right_length <= number_width_pre)) (PreH25 : (total_length = (left_length + right_length ))) (PreH26 : (2 <= total_length)) (PreH27 : (total_length <= (2 * number_width_pre ))) (PreH28 : (0 <= position)) (PreH29 : (position <= total_length)) (PreH30 : (RowsWellFormed rows lens count number_width_pre )) (PreH31 : (FlatRows flat rows count number_width_pre )) (PreH32 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (0 <= (((right_pre * number_width_pre ) + position ) - left_length )) ” 
  &&  “ ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre )) ” 
  &&  “ (0 <= (position - left_length )) ” 
  &&  “ ((position - left_length ) < number_width_pre) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (right_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (right_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position >= left_length) ” 
  &&  “ (position < total_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (2 <= total_length) ” 
  &&  “ (total_length <= (2 * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= total_length) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_then_left" ) )) # Int  |->_)
  **  ((( &( "left_then_right" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (left_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (left_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : (0 <= (position - left_length ))) (PreH8 : ((position - left_length ) < number_width_pre)) (PreH9 : (total_length <= INT_MAX)) (PreH10 : (right_length <= INT_MAX)) (PreH11 : (right_pre <= INT_MAX)) (PreH12 : (left_pre <= INT_MAX)) (PreH13 : (total_length >= INT_MIN)) (PreH14 : (right_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position >= left_length)) (PreH18 : (position < total_length)) (PreH19 : (1 <= count)) (PreH20 : (count <= 20)) (PreH21 : (1 <= number_width_pre)) (PreH22 : (number_width_pre <= 10)) (PreH23 : (0 <= left_pre)) (PreH24 : (left_pre < count)) (PreH25 : (0 <= right_pre)) (PreH26 : (right_pre < count)) (PreH27 : (1 <= left_length)) (PreH28 : (left_length <= number_width_pre)) (PreH29 : (1 <= right_length)) (PreH30 : (right_length <= number_width_pre)) (PreH31 : (total_length = (left_length + right_length ))) (PreH32 : (2 <= total_length)) (PreH33 : (total_length <= (2 * number_width_pre ))) (PreH34 : (0 <= position)) (PreH35 : (position <= total_length)) (PreH36 : (RowsWellFormed rows lens count number_width_pre )) (PreH37 : (FlatRows flat rows count number_width_pre )) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre )) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_5_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (left_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (left_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : (0 <= (position - left_length ))) (PreH8 : ((position - left_length ) < number_width_pre)) (PreH9 : (total_length <= INT_MAX)) (PreH10 : (right_length <= INT_MAX)) (PreH11 : (right_pre <= INT_MAX)) (PreH12 : (left_pre <= INT_MAX)) (PreH13 : (total_length >= INT_MIN)) (PreH14 : (right_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position >= left_length)) (PreH18 : (position < total_length)) (PreH19 : (1 <= count)) (PreH20 : (count <= 20)) (PreH21 : (1 <= number_width_pre)) (PreH22 : (number_width_pre <= 10)) (PreH23 : (0 <= left_pre)) (PreH24 : (left_pre < count)) (PreH25 : (0 <= right_pre)) (PreH26 : (right_pre < count)) (PreH27 : (1 <= left_length)) (PreH28 : (left_length <= number_width_pre)) (PreH29 : (1 <= right_length)) (PreH30 : (right_length <= number_width_pre)) (PreH31 : (total_length = (left_length + right_length ))) (PreH32 : (2 <= total_length)) (PreH33 : (total_length <= (2 * number_width_pre ))) (PreH34 : (0 <= position)) (PreH35 : (position <= total_length)) (PreH36 : (RowsWellFormed rows lens count number_width_pre )) (PreH37 : (FlatRows flat rows count number_width_pre )) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre ))
.

Definition compare_concatenated_order_entail_wit_6_1 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= ((left_pre * number_width_pre ) + position ))) (PreH2 : (((left_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (total_length >= INT_MIN)) (PreH11 : (right_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position < left_length)) (PreH16 : (position < total_length)) (PreH17 : (1 <= count)) (PreH18 : (count <= 20)) (PreH19 : (1 <= number_width_pre)) (PreH20 : (number_width_pre <= 10)) (PreH21 : (0 <= left_pre)) (PreH22 : (left_pre < count)) (PreH23 : (0 <= right_pre)) (PreH24 : (right_pre < count)) (PreH25 : (1 <= left_length)) (PreH26 : (left_length <= number_width_pre)) (PreH27 : (1 <= right_length)) (PreH28 : (right_length <= number_width_pre)) (PreH29 : (total_length = (left_length + right_length ))) (PreH30 : (2 <= total_length)) (PreH31 : (total_length <= (2 * number_width_pre ))) (PreH32 : (0 <= position)) (PreH33 : (position <= total_length)) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ ((Znth ((left_pre * number_width_pre ) + position ) flat 0) = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= ((left_pre * number_width_pre ) + position ))) (PreH2 : (((left_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (total_length >= INT_MIN)) (PreH11 : (right_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position < left_length)) (PreH16 : (position < total_length)) (PreH17 : (1 <= count)) (PreH18 : (count <= 20)) (PreH19 : (1 <= number_width_pre)) (PreH20 : (number_width_pre <= 10)) (PreH21 : (0 <= left_pre)) (PreH22 : (left_pre < count)) (PreH23 : (0 <= right_pre)) (PreH24 : (right_pre < count)) (PreH25 : (1 <= left_length)) (PreH26 : (left_length <= number_width_pre)) (PreH27 : (1 <= right_length)) (PreH28 : (right_length <= number_width_pre)) (PreH29 : (total_length = (left_length + right_length ))) (PreH30 : (2 <= total_length)) (PreH31 : (total_length <= (2 * number_width_pre ))) (PreH32 : (0 <= position)) (PreH33 : (position <= total_length)) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ ((Znth ((left_pre * number_width_pre ) + position ) flat 0) = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_6_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= ((left_pre * number_width_pre ) + position ))) (PreH2 : (((left_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (total_length >= INT_MIN)) (PreH11 : (right_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position < left_length)) (PreH16 : (position < total_length)) (PreH17 : (1 <= count)) (PreH18 : (count <= 20)) (PreH19 : (1 <= number_width_pre)) (PreH20 : (number_width_pre <= 10)) (PreH21 : (0 <= left_pre)) (PreH22 : (left_pre < count)) (PreH23 : (0 <= right_pre)) (PreH24 : (right_pre < count)) (PreH25 : (1 <= left_length)) (PreH26 : (left_length <= number_width_pre)) (PreH27 : (1 <= right_length)) (PreH28 : (right_length <= number_width_pre)) (PreH29 : (total_length = (left_length + right_length ))) (PreH30 : (2 <= total_length)) (PreH31 : (total_length <= (2 * number_width_pre ))) (PreH32 : (0 <= position)) (PreH33 : (position <= total_length)) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((Znth ((left_pre * number_width_pre ) + position ) flat 0) = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))
.

Definition compare_concatenated_order_entail_wit_6_2 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= (((right_pre * number_width_pre ) + position ) - left_length ))) (PreH2 : ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - left_length ))) (PreH4 : ((position - left_length ) < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (right_pre <= INT_MAX)) (PreH8 : (left_pre <= INT_MAX)) (PreH9 : (total_length >= INT_MIN)) (PreH10 : (right_length >= INT_MIN)) (PreH11 : (right_pre >= INT_MIN)) (PreH12 : (left_pre >= INT_MIN)) (PreH13 : (position >= left_length)) (PreH14 : (position < total_length)) (PreH15 : (1 <= count)) (PreH16 : (count <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre < count)) (PreH21 : (0 <= right_pre)) (PreH22 : (right_pre < count)) (PreH23 : (1 <= left_length)) (PreH24 : (left_length <= number_width_pre)) (PreH25 : (1 <= right_length)) (PreH26 : (right_length <= number_width_pre)) (PreH27 : (total_length = (left_length + right_length ))) (PreH28 : (2 <= total_length)) (PreH29 : (total_length <= (2 * number_width_pre ))) (PreH30 : (0 <= position)) (PreH31 : (position <= total_length)) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ ((Znth (((right_pre * number_width_pre ) + position ) - left_length ) flat 0) = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= (((right_pre * number_width_pre ) + position ) - left_length ))) (PreH2 : ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - left_length ))) (PreH4 : ((position - left_length ) < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (right_pre <= INT_MAX)) (PreH8 : (left_pre <= INT_MAX)) (PreH9 : (total_length >= INT_MIN)) (PreH10 : (right_length >= INT_MIN)) (PreH11 : (right_pre >= INT_MIN)) (PreH12 : (left_pre >= INT_MIN)) (PreH13 : (position >= left_length)) (PreH14 : (position < total_length)) (PreH15 : (1 <= count)) (PreH16 : (count <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre < count)) (PreH21 : (0 <= right_pre)) (PreH22 : (right_pre < count)) (PreH23 : (1 <= left_length)) (PreH24 : (left_length <= number_width_pre)) (PreH25 : (1 <= right_length)) (PreH26 : (right_length <= number_width_pre)) (PreH27 : (total_length = (left_length + right_length ))) (PreH28 : (2 <= total_length)) (PreH29 : (total_length <= (2 * number_width_pre ))) (PreH30 : (0 <= position)) (PreH31 : (position <= total_length)) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ ((Znth (((right_pre * number_width_pre ) + position ) - left_length ) flat 0) = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_6_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= (((right_pre * number_width_pre ) + position ) - left_length ))) (PreH2 : ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - left_length ))) (PreH4 : ((position - left_length ) < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (right_pre <= INT_MAX)) (PreH8 : (left_pre <= INT_MAX)) (PreH9 : (total_length >= INT_MIN)) (PreH10 : (right_length >= INT_MIN)) (PreH11 : (right_pre >= INT_MIN)) (PreH12 : (left_pre >= INT_MIN)) (PreH13 : (position >= left_length)) (PreH14 : (position < total_length)) (PreH15 : (1 <= count)) (PreH16 : (count <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre < count)) (PreH21 : (0 <= right_pre)) (PreH22 : (right_pre < count)) (PreH23 : (1 <= left_length)) (PreH24 : (left_length <= number_width_pre)) (PreH25 : (1 <= right_length)) (PreH26 : (right_length <= number_width_pre)) (PreH27 : (total_length = (left_length + right_length ))) (PreH28 : (2 <= total_length)) (PreH29 : (total_length <= (2 * number_width_pre ))) (PreH30 : (0 <= position)) (PreH31 : (position <= total_length)) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((Znth (((right_pre * number_width_pre ) + position ) - left_length ) flat 0) = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))
.

Definition compare_concatenated_order_entail_wit_7 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (position < right_length)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (0 <= position)) (PreH16 : (position < total_length)) (PreH17 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH18 : (RowsWellFormed rows lens count number_width_pre )) (PreH19 : (FlatRows flat rows count number_width_pre )) (PreH20 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
|--
  “ (0 <= position) ” 
  &&  “ (position < number_width_pre) ” 
  &&  “ (left_then_right <= INT_MAX) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (right_length <= INT_MAX) ” 
  &&  “ (left_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (left_then_right >= INT_MIN) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (right_length >= INT_MIN) ” 
  &&  “ (left_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position < right_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
.

Definition compare_concatenated_order_entail_wit_8 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= position)) (PreH2 : (position < number_width_pre)) (PreH3 : (left_then_right <= INT_MAX)) (PreH4 : (total_length <= INT_MAX)) (PreH5 : (right_length <= INT_MAX)) (PreH6 : (left_length <= INT_MAX)) (PreH7 : (right_pre <= INT_MAX)) (PreH8 : (left_pre <= INT_MAX)) (PreH9 : (left_then_right >= INT_MIN)) (PreH10 : (total_length >= INT_MIN)) (PreH11 : (right_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position < right_length)) (PreH16 : (1 <= count)) (PreH17 : (count <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre < count)) (PreH22 : (0 <= right_pre)) (PreH23 : (right_pre < count)) (PreH24 : (1 <= left_length)) (PreH25 : (left_length <= number_width_pre)) (PreH26 : (1 <= right_length)) (PreH27 : (right_length <= number_width_pre)) (PreH28 : (total_length = (left_length + right_length ))) (PreH29 : (0 <= position)) (PreH30 : (position < total_length)) (PreH31 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
|--
  “ (0 <= ((right_pre * number_width_pre ) + position )) ” 
  &&  “ (((right_pre * number_width_pre ) + position ) < (count * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < number_width_pre) ” 
  &&  “ (left_then_right <= INT_MAX) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (right_length <= INT_MAX) ” 
  &&  “ (left_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (left_then_right >= INT_MIN) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (right_length >= INT_MIN) ” 
  &&  “ (left_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position < right_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : (0 <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (left_then_right <= INT_MAX)) (PreH8 : (total_length <= INT_MAX)) (PreH9 : (right_length <= INT_MAX)) (PreH10 : (left_length <= INT_MAX)) (PreH11 : (right_pre <= INT_MAX)) (PreH12 : (left_pre <= INT_MAX)) (PreH13 : (left_then_right >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (right_length >= INT_MIN)) (PreH16 : (left_length >= INT_MIN)) (PreH17 : (right_pre >= INT_MIN)) (PreH18 : (left_pre >= INT_MIN)) (PreH19 : (position < right_length)) (PreH20 : (1 <= count)) (PreH21 : (count <= 20)) (PreH22 : (1 <= number_width_pre)) (PreH23 : (number_width_pre <= 10)) (PreH24 : (0 <= left_pre)) (PreH25 : (left_pre < count)) (PreH26 : (0 <= right_pre)) (PreH27 : (right_pre < count)) (PreH28 : (1 <= left_length)) (PreH29 : (left_length <= number_width_pre)) (PreH30 : (1 <= right_length)) (PreH31 : (right_length <= number_width_pre)) (PreH32 : (total_length = (left_length + right_length ))) (PreH33 : (0 <= position)) (PreH34 : (position < total_length)) (PreH35 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH36 : (RowsWellFormed rows lens count number_width_pre )) (PreH37 : (FlatRows flat rows count number_width_pre )) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ (((right_pre * number_width_pre ) + position ) < (count * number_width_pre )) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_8_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (number_width_pre >= INT_MIN)) (PreH4 : (position >= INT_MIN)) (PreH5 : (0 <= position)) (PreH6 : (position < number_width_pre)) (PreH7 : (left_then_right <= INT_MAX)) (PreH8 : (total_length <= INT_MAX)) (PreH9 : (right_length <= INT_MAX)) (PreH10 : (left_length <= INT_MAX)) (PreH11 : (right_pre <= INT_MAX)) (PreH12 : (left_pre <= INT_MAX)) (PreH13 : (left_then_right >= INT_MIN)) (PreH14 : (total_length >= INT_MIN)) (PreH15 : (right_length >= INT_MIN)) (PreH16 : (left_length >= INT_MIN)) (PreH17 : (right_pre >= INT_MIN)) (PreH18 : (left_pre >= INT_MIN)) (PreH19 : (position < right_length)) (PreH20 : (1 <= count)) (PreH21 : (count <= 20)) (PreH22 : (1 <= number_width_pre)) (PreH23 : (number_width_pre <= 10)) (PreH24 : (0 <= left_pre)) (PreH25 : (left_pre < count)) (PreH26 : (0 <= right_pre)) (PreH27 : (right_pre < count)) (PreH28 : (1 <= left_length)) (PreH29 : (left_length <= number_width_pre)) (PreH30 : (1 <= right_length)) (PreH31 : (right_length <= number_width_pre)) (PreH32 : (total_length = (left_length + right_length ))) (PreH33 : (0 <= position)) (PreH34 : (position < total_length)) (PreH35 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH36 : (RowsWellFormed rows lens count number_width_pre )) (PreH37 : (FlatRows flat rows count number_width_pre )) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (((right_pre * number_width_pre ) + position ) < (count * number_width_pre ))
.

Definition compare_concatenated_order_entail_wit_9 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (position >= right_length)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (0 <= position)) (PreH16 : (position < total_length)) (PreH17 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH18 : (RowsWellFormed rows lens count number_width_pre )) (PreH19 : (FlatRows flat rows count number_width_pre )) (PreH20 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
|--
  “ (0 <= (position - right_length )) ” 
  &&  “ ((position - right_length ) < number_width_pre) ” 
  &&  “ (left_then_right <= INT_MAX) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (left_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (left_then_right >= INT_MIN) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (left_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position >= right_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
.

Definition compare_concatenated_order_entail_wit_10 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= (position - right_length ))) (PreH2 : ((position - right_length ) < number_width_pre)) (PreH3 : (left_then_right <= INT_MAX)) (PreH4 : (total_length <= INT_MAX)) (PreH5 : (left_length <= INT_MAX)) (PreH6 : (right_pre <= INT_MAX)) (PreH7 : (left_pre <= INT_MAX)) (PreH8 : (left_then_right >= INT_MIN)) (PreH9 : (total_length >= INT_MIN)) (PreH10 : (left_length >= INT_MIN)) (PreH11 : (right_pre >= INT_MIN)) (PreH12 : (left_pre >= INT_MIN)) (PreH13 : (position >= right_length)) (PreH14 : (1 <= count)) (PreH15 : (count <= 20)) (PreH16 : (1 <= number_width_pre)) (PreH17 : (number_width_pre <= 10)) (PreH18 : (0 <= left_pre)) (PreH19 : (left_pre < count)) (PreH20 : (0 <= right_pre)) (PreH21 : (right_pre < count)) (PreH22 : (1 <= left_length)) (PreH23 : (left_length <= number_width_pre)) (PreH24 : (1 <= right_length)) (PreH25 : (right_length <= number_width_pre)) (PreH26 : (total_length = (left_length + right_length ))) (PreH27 : (0 <= position)) (PreH28 : (position < total_length)) (PreH29 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH30 : (RowsWellFormed rows lens count number_width_pre )) (PreH31 : (FlatRows flat rows count number_width_pre )) (PreH32 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
|--
  “ (0 <= (((left_pre * number_width_pre ) + position ) - right_length )) ” 
  &&  “ ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre )) ” 
  &&  “ (0 <= (position - right_length )) ” 
  &&  “ ((position - right_length ) < number_width_pre) ” 
  &&  “ (left_then_right <= INT_MAX) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (left_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (left_then_right >= INT_MIN) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (left_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position >= right_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "right_length" ) )) # Int  |-> right_length)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left_length" ) )) # Int  |-> left_length)
  **  ((( &( "total_length" ) )) # Int  |-> total_length)
  **  ((( &( "left_then_right" ) )) # Int  |-> left_then_right)
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
  **  ((( &( "right_then_left" ) )) # Int  |->_)
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (right_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (right_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : (0 <= (position - right_length ))) (PreH8 : ((position - right_length ) < number_width_pre)) (PreH9 : (left_then_right <= INT_MAX)) (PreH10 : (total_length <= INT_MAX)) (PreH11 : (left_length <= INT_MAX)) (PreH12 : (right_pre <= INT_MAX)) (PreH13 : (left_pre <= INT_MAX)) (PreH14 : (left_then_right >= INT_MIN)) (PreH15 : (total_length >= INT_MIN)) (PreH16 : (left_length >= INT_MIN)) (PreH17 : (right_pre >= INT_MIN)) (PreH18 : (left_pre >= INT_MIN)) (PreH19 : (position >= right_length)) (PreH20 : (1 <= count)) (PreH21 : (count <= 20)) (PreH22 : (1 <= number_width_pre)) (PreH23 : (number_width_pre <= 10)) (PreH24 : (0 <= left_pre)) (PreH25 : (left_pre < count)) (PreH26 : (0 <= right_pre)) (PreH27 : (right_pre < count)) (PreH28 : (1 <= left_length)) (PreH29 : (left_length <= number_width_pre)) (PreH30 : (1 <= right_length)) (PreH31 : (right_length <= number_width_pre)) (PreH32 : (total_length = (left_length + right_length ))) (PreH33 : (0 <= position)) (PreH34 : (position < total_length)) (PreH35 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH36 : (RowsWellFormed rows lens count number_width_pre )) (PreH37 : (FlatRows flat rows count number_width_pre )) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre )) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_10_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (number_width_pre <= INT_MAX)) (PreH2 : (right_length <= INT_MAX)) (PreH3 : (position <= INT_MAX)) (PreH4 : (number_width_pre >= INT_MIN)) (PreH5 : (right_length >= INT_MIN)) (PreH6 : (position >= INT_MIN)) (PreH7 : (0 <= (position - right_length ))) (PreH8 : ((position - right_length ) < number_width_pre)) (PreH9 : (left_then_right <= INT_MAX)) (PreH10 : (total_length <= INT_MAX)) (PreH11 : (left_length <= INT_MAX)) (PreH12 : (right_pre <= INT_MAX)) (PreH13 : (left_pre <= INT_MAX)) (PreH14 : (left_then_right >= INT_MIN)) (PreH15 : (total_length >= INT_MIN)) (PreH16 : (left_length >= INT_MIN)) (PreH17 : (right_pre >= INT_MIN)) (PreH18 : (left_pre >= INT_MIN)) (PreH19 : (position >= right_length)) (PreH20 : (1 <= count)) (PreH21 : (count <= 20)) (PreH22 : (1 <= number_width_pre)) (PreH23 : (number_width_pre <= 10)) (PreH24 : (0 <= left_pre)) (PreH25 : (left_pre < count)) (PreH26 : (0 <= right_pre)) (PreH27 : (right_pre < count)) (PreH28 : (1 <= left_length)) (PreH29 : (left_length <= number_width_pre)) (PreH30 : (1 <= right_length)) (PreH31 : (right_length <= number_width_pre)) (PreH32 : (total_length = (left_length + right_length ))) (PreH33 : (0 <= position)) (PreH34 : (position < total_length)) (PreH35 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH36 : (RowsWellFormed rows lens count number_width_pre )) (PreH37 : (FlatRows flat rows count number_width_pre )) (PreH38 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre ))
.

Definition compare_concatenated_order_entail_wit_11_1 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= ((right_pre * number_width_pre ) + position ))) (PreH2 : (((right_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (right_length <= INT_MAX)) (PreH8 : (left_length <= INT_MAX)) (PreH9 : (right_pre <= INT_MAX)) (PreH10 : (left_pre <= INT_MAX)) (PreH11 : (left_then_right >= INT_MIN)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (right_length >= INT_MIN)) (PreH14 : (left_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position < right_length)) (PreH18 : (1 <= count)) (PreH19 : (count <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : (0 <= left_pre)) (PreH23 : (left_pre < count)) (PreH24 : (0 <= right_pre)) (PreH25 : (right_pre < count)) (PreH26 : (1 <= left_length)) (PreH27 : (left_length <= number_width_pre)) (PreH28 : (1 <= right_length)) (PreH29 : (right_length <= number_width_pre)) (PreH30 : (total_length = (left_length + right_length ))) (PreH31 : (0 <= position)) (PreH32 : (position < total_length)) (PreH33 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ ((Znth ((right_pre * number_width_pre ) + position ) flat 0) = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= ((right_pre * number_width_pre ) + position ))) (PreH2 : (((right_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (right_length <= INT_MAX)) (PreH8 : (left_length <= INT_MAX)) (PreH9 : (right_pre <= INT_MAX)) (PreH10 : (left_pre <= INT_MAX)) (PreH11 : (left_then_right >= INT_MIN)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (right_length >= INT_MIN)) (PreH14 : (left_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position < right_length)) (PreH18 : (1 <= count)) (PreH19 : (count <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : (0 <= left_pre)) (PreH23 : (left_pre < count)) (PreH24 : (0 <= right_pre)) (PreH25 : (right_pre < count)) (PreH26 : (1 <= left_length)) (PreH27 : (left_length <= number_width_pre)) (PreH28 : (1 <= right_length)) (PreH29 : (right_length <= number_width_pre)) (PreH30 : (total_length = (left_length + right_length ))) (PreH31 : (0 <= position)) (PreH32 : (position < total_length)) (PreH33 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ ((Znth ((right_pre * number_width_pre ) + position ) flat 0) = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position))) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_11_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= ((right_pre * number_width_pre ) + position ))) (PreH2 : (((right_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (right_length <= INT_MAX)) (PreH8 : (left_length <= INT_MAX)) (PreH9 : (right_pre <= INT_MAX)) (PreH10 : (left_pre <= INT_MAX)) (PreH11 : (left_then_right >= INT_MIN)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (right_length >= INT_MIN)) (PreH14 : (left_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position < right_length)) (PreH18 : (1 <= count)) (PreH19 : (count <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : (0 <= left_pre)) (PreH23 : (left_pre < count)) (PreH24 : (0 <= right_pre)) (PreH25 : (right_pre < count)) (PreH26 : (1 <= left_length)) (PreH27 : (left_length <= number_width_pre)) (PreH28 : (1 <= right_length)) (PreH29 : (right_length <= number_width_pre)) (PreH30 : (total_length = (left_length + right_length ))) (PreH31 : (0 <= position)) (PreH32 : (position < total_length)) (PreH33 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((Znth ((right_pre * number_width_pre ) + position ) flat 0) = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))
.

Definition compare_concatenated_order_entail_wit_11_2 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= (((left_pre * number_width_pre ) + position ) - right_length ))) (PreH2 : ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - right_length ))) (PreH4 : ((position - right_length ) < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (left_then_right >= INT_MIN)) (PreH11 : (total_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position >= right_length)) (PreH16 : (1 <= count)) (PreH17 : (count <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre < count)) (PreH22 : (0 <= right_pre)) (PreH23 : (right_pre < count)) (PreH24 : (1 <= left_length)) (PreH25 : (left_length <= number_width_pre)) (PreH26 : (1 <= right_length)) (PreH27 : (right_length <= number_width_pre)) (PreH28 : (total_length = (left_length + right_length ))) (PreH29 : (0 <= position)) (PreH30 : (position < total_length)) (PreH31 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ ((Znth (((left_pre * number_width_pre ) + position ) - right_length ) flat 0) = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= (((left_pre * number_width_pre ) + position ) - right_length ))) (PreH2 : ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - right_length ))) (PreH4 : ((position - right_length ) < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (left_then_right >= INT_MIN)) (PreH11 : (total_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position >= right_length)) (PreH16 : (1 <= count)) (PreH17 : (count <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre < count)) (PreH22 : (0 <= right_pre)) (PreH23 : (right_pre < count)) (PreH24 : (1 <= left_length)) (PreH25 : (left_length <= number_width_pre)) (PreH26 : (1 <= right_length)) (PreH27 : (right_length <= number_width_pre)) (PreH28 : (total_length = (left_length + right_length ))) (PreH29 : (0 <= position)) (PreH30 : (position < total_length)) (PreH31 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ ((Znth (((left_pre * number_width_pre ) + position ) - right_length ) flat 0) = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position))) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_11_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= (((left_pre * number_width_pre ) + position ) - right_length ))) (PreH2 : ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - right_length ))) (PreH4 : ((position - right_length ) < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (left_then_right >= INT_MIN)) (PreH11 : (total_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position >= right_length)) (PreH16 : (1 <= count)) (PreH17 : (count <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre < count)) (PreH22 : (0 <= right_pre)) (PreH23 : (right_pre < count)) (PreH24 : (1 <= left_length)) (PreH25 : (left_length <= number_width_pre)) (PreH26 : (1 <= right_length)) (PreH27 : (right_length <= number_width_pre)) (PreH28 : (total_length = (left_length + right_length ))) (PreH29 : (0 <= position)) (PreH30 : (position < total_length)) (PreH31 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  ((Znth (((left_pre * number_width_pre ) + position ) - right_length ) flat 0) = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))
.

Definition compare_concatenated_order_entail_wit_12 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right >= right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (0 <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (2 <= total_length) ” 
  &&  “ (total_length <= (2 * number_width_pre )) ” 
  &&  “ (0 <= (position + 1 )) ” 
  &&  “ ((position + 1 ) <= total_length) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length (position + 1 ) ) ”
  &&  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right >= right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (0 <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length (position + 1 ) ) ”
  &&  emp
).

Definition compare_concatenated_order_entail_wit_12_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right >= right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (0 <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length (position + 1 ) )
.

Definition compare_concatenated_order_return_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (position >= total_length)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (2 <= total_length)) (PreH16 : (total_length <= (2 * number_width_pre ))) (PreH17 : (0 <= position)) (PreH18 : (position <= total_length)) (PreH19 : (RowsWellFormed rows lens count number_width_pre )) (PreH20 : (FlatRows flat rows count number_width_pre )) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (ConcatCompareSignOutcome rows lens left_pre right_pre 0 ) ”
  &&  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (position >= total_length)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (2 <= total_length)) (PreH16 : (total_length <= (2 * number_width_pre ))) (PreH17 : (0 <= position)) (PreH18 : (position <= total_length)) (PreH19 : (RowsWellFormed rows lens count number_width_pre )) (PreH20 : (FlatRows flat rows count number_width_pre )) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ (ConcatCompareSignOutcome rows lens left_pre right_pre 0 ) ”
  &&  emp
).

Definition compare_concatenated_order_return_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (position >= total_length)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (2 <= total_length)) (PreH16 : (total_length <= (2 * number_width_pre ))) (PreH17 : (0 <= position)) (PreH18 : (position <= total_length)) (PreH19 : (RowsWellFormed rows lens count number_width_pre )) (PreH20 : (FlatRows flat rows count number_width_pre )) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (ConcatCompareSignOutcome rows lens left_pre right_pre 0 )
.

Definition compare_concatenated_order_return_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right < right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (0 <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (ConcatCompareSignOutcome rows lens left_pre right_pre (-1) ) ”
  &&  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right < right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (0 <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ (ConcatCompareSignOutcome rows lens left_pre right_pre (-1) ) ”
  &&  emp
).

Definition compare_concatenated_order_return_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right < right_then_left)) (PreH2 : (left_then_right <= right_then_left)) (PreH3 : (1 <= count)) (PreH4 : (count <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre < count)) (PreH9 : (0 <= right_pre)) (PreH10 : (right_pre < count)) (PreH11 : (1 <= left_length)) (PreH12 : (left_length <= number_width_pre)) (PreH13 : (1 <= right_length)) (PreH14 : (right_length <= number_width_pre)) (PreH15 : (total_length = (left_length + right_length ))) (PreH16 : (0 <= position)) (PreH17 : (position < total_length)) (PreH18 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH20 : (RowsWellFormed rows lens count number_width_pre )) (PreH21 : (FlatRows flat rows count number_width_pre )) (PreH22 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (ConcatCompareSignOutcome rows lens left_pre right_pre (-1) )
.

Definition compare_concatenated_order_return_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right > right_then_left)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (0 <= position)) (PreH16 : (position < total_length)) (PreH17 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH18 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (RowsWellFormed rows lens count number_width_pre )) (PreH20 : (FlatRows flat rows count number_width_pre )) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (ConcatCompareSignOutcome rows lens left_pre right_pre 1 ) ”
  &&  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
) \/
(
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right > right_then_left)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (0 <= position)) (PreH16 : (position < total_length)) (PreH17 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH18 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (RowsWellFormed rows lens count number_width_pre )) (PreH20 : (FlatRows flat rows count number_width_pre )) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  TT && emp 
|--
  “ (ConcatCompareSignOutcome rows lens left_pre right_pre 1 ) ”
  &&  emp
).

Definition compare_concatenated_order_return_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (right_then_left: Z) (PreH1 : (left_then_right > right_then_left)) (PreH2 : (1 <= count)) (PreH3 : (count <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (0 <= left_pre)) (PreH7 : (left_pre < count)) (PreH8 : (0 <= right_pre)) (PreH9 : (right_pre < count)) (PreH10 : (1 <= left_length)) (PreH11 : (left_length <= number_width_pre)) (PreH12 : (1 <= right_length)) (PreH13 : (right_length <= number_width_pre)) (PreH14 : (total_length = (left_length + right_length ))) (PreH15 : (0 <= position)) (PreH16 : (position < total_length)) (PreH17 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH18 : (right_then_left = (ConcatRightDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH19 : (RowsWellFormed rows lens count number_width_pre )) (PreH20 : (FlatRows flat rows count number_width_pre )) (PreH21 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (ConcatCompareSignOutcome rows lens left_pre right_pre 1 )
.

Definition compare_concatenated_order_partial_solve_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ”
  &&  (((lengths_pre + (left_pre * sizeof(INT)))) # Int  |-> (Znth left_pre lens 0))
  **  (IntArray.missing_i lengths_pre left_pre 0 count lens )
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
.

Definition compare_concatenated_order_partial_solve_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count)) (PreH2 : (count <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre < count)) (PreH7 : (0 <= right_pre)) (PreH8 : (right_pre < count)) (PreH9 : (RowsWellFormed rows lens count number_width_pre )) (PreH10 : (FlatRows flat rows count number_width_pre )) ,
  (IntArray.full lengths_pre count lens )
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
|--
  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ”
  &&  (((lengths_pre + (right_pre * sizeof(INT)))) # Int  |-> (Znth right_pre lens 0))
  **  (IntArray.missing_i lengths_pre right_pre 0 count lens )
  **  (IntArray.full numbers_pre (count * number_width_pre ) flat )
.

Definition compare_concatenated_order_partial_solve_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= ((left_pre * number_width_pre ) + position ))) (PreH2 : (((left_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (total_length >= INT_MIN)) (PreH11 : (right_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position < left_length)) (PreH16 : (position < total_length)) (PreH17 : (1 <= count)) (PreH18 : (count <= 20)) (PreH19 : (1 <= number_width_pre)) (PreH20 : (number_width_pre <= 10)) (PreH21 : (0 <= left_pre)) (PreH22 : (left_pre < count)) (PreH23 : (0 <= right_pre)) (PreH24 : (right_pre < count)) (PreH25 : (1 <= left_length)) (PreH26 : (left_length <= number_width_pre)) (PreH27 : (1 <= right_length)) (PreH28 : (right_length <= number_width_pre)) (PreH29 : (total_length = (left_length + right_length ))) (PreH30 : (2 <= total_length)) (PreH31 : (total_length <= (2 * number_width_pre ))) (PreH32 : (0 <= position)) (PreH33 : (position <= total_length)) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (0 <= ((left_pre * number_width_pre ) + position )) ” 
  &&  “ (((left_pre * number_width_pre ) + position ) < (count * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < number_width_pre) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (right_length <= INT_MAX) ” 
  &&  “ (left_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (right_length >= INT_MIN) ” 
  &&  “ (left_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position < left_length) ” 
  &&  “ (position < total_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (2 <= total_length) ” 
  &&  “ (total_length <= (2 * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= total_length) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  (((numbers_pre + (((left_pre * number_width_pre ) + position ) * sizeof(INT)))) # Int  |-> (Znth ((left_pre * number_width_pre ) + position ) flat 0))
  **  (IntArray.missing_i numbers_pre ((left_pre * number_width_pre ) + position ) 0 (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
.

Definition compare_concatenated_order_partial_solve_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (position: Z) (total_length: Z) (right_length: Z) (left_length: Z) (PreH1 : (0 <= (((right_pre * number_width_pre ) + position ) - left_length ))) (PreH2 : ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - left_length ))) (PreH4 : ((position - left_length ) < number_width_pre)) (PreH5 : (total_length <= INT_MAX)) (PreH6 : (right_length <= INT_MAX)) (PreH7 : (right_pre <= INT_MAX)) (PreH8 : (left_pre <= INT_MAX)) (PreH9 : (total_length >= INT_MIN)) (PreH10 : (right_length >= INT_MIN)) (PreH11 : (right_pre >= INT_MIN)) (PreH12 : (left_pre >= INT_MIN)) (PreH13 : (position >= left_length)) (PreH14 : (position < total_length)) (PreH15 : (1 <= count)) (PreH16 : (count <= 20)) (PreH17 : (1 <= number_width_pre)) (PreH18 : (number_width_pre <= 10)) (PreH19 : (0 <= left_pre)) (PreH20 : (left_pre < count)) (PreH21 : (0 <= right_pre)) (PreH22 : (right_pre < count)) (PreH23 : (1 <= left_length)) (PreH24 : (left_length <= number_width_pre)) (PreH25 : (1 <= right_length)) (PreH26 : (right_length <= number_width_pre)) (PreH27 : (total_length = (left_length + right_length ))) (PreH28 : (2 <= total_length)) (PreH29 : (total_length <= (2 * number_width_pre ))) (PreH30 : (0 <= position)) (PreH31 : (position <= total_length)) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (0 <= (((right_pre * number_width_pre ) + position ) - left_length )) ” 
  &&  “ ((((right_pre * number_width_pre ) + position ) - left_length ) < (count * number_width_pre )) ” 
  &&  “ (0 <= (position - left_length )) ” 
  &&  “ ((position - left_length ) < number_width_pre) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (right_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (right_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position >= left_length) ” 
  &&  “ (position < total_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (2 <= total_length) ” 
  &&  “ (total_length <= (2 * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= total_length) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  (((numbers_pre + ((((right_pre * number_width_pre ) + position ) - left_length ) * sizeof(INT)))) # Int  |-> (Znth (((right_pre * number_width_pre ) + position ) - left_length ) flat 0))
  **  (IntArray.missing_i numbers_pre (((right_pre * number_width_pre ) + position ) - left_length ) 0 (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
.

Definition compare_concatenated_order_partial_solve_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= ((right_pre * number_width_pre ) + position ))) (PreH2 : (((right_pre * number_width_pre ) + position ) < (count * number_width_pre ))) (PreH3 : (0 <= position)) (PreH4 : (position < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (right_length <= INT_MAX)) (PreH8 : (left_length <= INT_MAX)) (PreH9 : (right_pre <= INT_MAX)) (PreH10 : (left_pre <= INT_MAX)) (PreH11 : (left_then_right >= INT_MIN)) (PreH12 : (total_length >= INT_MIN)) (PreH13 : (right_length >= INT_MIN)) (PreH14 : (left_length >= INT_MIN)) (PreH15 : (right_pre >= INT_MIN)) (PreH16 : (left_pre >= INT_MIN)) (PreH17 : (position < right_length)) (PreH18 : (1 <= count)) (PreH19 : (count <= 20)) (PreH20 : (1 <= number_width_pre)) (PreH21 : (number_width_pre <= 10)) (PreH22 : (0 <= left_pre)) (PreH23 : (left_pre < count)) (PreH24 : (0 <= right_pre)) (PreH25 : (right_pre < count)) (PreH26 : (1 <= left_length)) (PreH27 : (left_length <= number_width_pre)) (PreH28 : (1 <= right_length)) (PreH29 : (right_length <= number_width_pre)) (PreH30 : (total_length = (left_length + right_length ))) (PreH31 : (0 <= position)) (PreH32 : (position < total_length)) (PreH33 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH34 : (RowsWellFormed rows lens count number_width_pre )) (PreH35 : (FlatRows flat rows count number_width_pre )) (PreH36 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (0 <= ((right_pre * number_width_pre ) + position )) ” 
  &&  “ (((right_pre * number_width_pre ) + position ) < (count * number_width_pre )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < number_width_pre) ” 
  &&  “ (left_then_right <= INT_MAX) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (right_length <= INT_MAX) ” 
  &&  “ (left_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (left_then_right >= INT_MIN) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (right_length >= INT_MIN) ” 
  &&  “ (left_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position < right_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  (((numbers_pre + (((right_pre * number_width_pre ) + position ) * sizeof(INT)))) # Int  |-> (Znth ((right_pre * number_width_pre ) + position ) flat 0))
  **  (IntArray.missing_i numbers_pre ((right_pre * number_width_pre ) + position ) 0 (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
.

Definition compare_concatenated_order_partial_solve_wit_6 := 
forall (right_pre: Z) (left_pre: Z) (number_width_pre: Z) (lengths_pre: Z) (numbers_pre: Z) (count: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (left_length: Z) (right_length: Z) (total_length: Z) (position: Z) (left_then_right: Z) (PreH1 : (0 <= (((left_pre * number_width_pre ) + position ) - right_length ))) (PreH2 : ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre ))) (PreH3 : (0 <= (position - right_length ))) (PreH4 : ((position - right_length ) < number_width_pre)) (PreH5 : (left_then_right <= INT_MAX)) (PreH6 : (total_length <= INT_MAX)) (PreH7 : (left_length <= INT_MAX)) (PreH8 : (right_pre <= INT_MAX)) (PreH9 : (left_pre <= INT_MAX)) (PreH10 : (left_then_right >= INT_MIN)) (PreH11 : (total_length >= INT_MIN)) (PreH12 : (left_length >= INT_MIN)) (PreH13 : (right_pre >= INT_MIN)) (PreH14 : (left_pre >= INT_MIN)) (PreH15 : (position >= right_length)) (PreH16 : (1 <= count)) (PreH17 : (count <= 20)) (PreH18 : (1 <= number_width_pre)) (PreH19 : (number_width_pre <= 10)) (PreH20 : (0 <= left_pre)) (PreH21 : (left_pre < count)) (PreH22 : (0 <= right_pre)) (PreH23 : (right_pre < count)) (PreH24 : (1 <= left_length)) (PreH25 : (left_length <= number_width_pre)) (PreH26 : (1 <= right_length)) (PreH27 : (right_length <= number_width_pre)) (PreH28 : (total_length = (left_length + right_length ))) (PreH29 : (0 <= position)) (PreH30 : (position < total_length)) (PreH31 : (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position)))) (PreH32 : (RowsWellFormed rows lens count number_width_pre )) (PreH33 : (FlatRows flat rows count number_width_pre )) (PreH34 : (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position )) ,
  (IntArray.full numbers_pre (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
|--
  “ (0 <= (((left_pre * number_width_pre ) + position ) - right_length )) ” 
  &&  “ ((((left_pre * number_width_pre ) + position ) - right_length ) < (count * number_width_pre )) ” 
  &&  “ (0 <= (position - right_length )) ” 
  &&  “ ((position - right_length ) < number_width_pre) ” 
  &&  “ (left_then_right <= INT_MAX) ” 
  &&  “ (total_length <= INT_MAX) ” 
  &&  “ (left_length <= INT_MAX) ” 
  &&  “ (right_pre <= INT_MAX) ” 
  &&  “ (left_pre <= INT_MAX) ” 
  &&  “ (left_then_right >= INT_MIN) ” 
  &&  “ (total_length >= INT_MIN) ” 
  &&  “ (left_length >= INT_MIN) ” 
  &&  “ (right_pre >= INT_MIN) ” 
  &&  “ (left_pre >= INT_MIN) ” 
  &&  “ (position >= right_length) ” 
  &&  “ (1 <= count) ” 
  &&  “ (count <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre < count) ” 
  &&  “ (0 <= right_pre) ” 
  &&  “ (right_pre < count) ” 
  &&  “ (1 <= left_length) ” 
  &&  “ (left_length <= number_width_pre) ” 
  &&  “ (1 <= right_length) ” 
  &&  “ (right_length <= number_width_pre) ” 
  &&  “ (total_length = (left_length + right_length )) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position < total_length) ” 
  &&  “ (left_then_right = (ConcatLeftDigit (rows) (lens) (left_pre) (right_pre) (position))) ” 
  &&  “ (RowsWellFormed rows lens count number_width_pre ) ” 
  &&  “ (FlatRows flat rows count number_width_pre ) ” 
  &&  “ (ConcatCompareLoopState rows lens left_pre right_pre left_length right_length position ) ”
  &&  (((numbers_pre + ((((left_pre * number_width_pre ) + position ) - right_length ) * sizeof(INT)))) # Int  |-> (Znth (((left_pre * number_width_pre ) + position ) - right_length ) flat 0))
  **  (IntArray.missing_i numbers_pre (((left_pre * number_width_pre ) + position ) - right_length ) 0 (count * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count lens )
.

(*----- Function concatenating_numbers_dp -----*)

Definition concatenating_numbers_dp_safety_wit_1 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((signed_last_nbits ((1 * (2^count_pre) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^count_pre) )) (32))) ” 
  &&  “ (count_pre <= 31) ” 
  &&  “ (0 <= count_pre) ”
) \/
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((signed_last_nbits ((1 * (2^count_pre) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^count_pre) )) (32))) ” 
  &&  “ (count_pre <= 31) ” 
  &&  “ (0 <= count_pre) ”
).

Definition concatenating_numbers_dp_safety_wit_1_split_goal_1 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((signed_last_nbits ((1 * (2^count_pre) )) (32)) <= INT_MAX) ”
.

Definition concatenating_numbers_dp_safety_wit_1_split_goal_2 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^count_pre) )) (32))) ”
.

Definition concatenating_numbers_dp_safety_wit_1_split_goal_3 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (count_pre <= 31) ”
.

Definition concatenating_numbers_dp_safety_wit_1_split_goal_4 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= count_pre) ”
.

Definition concatenating_numbers_dp_safety_wit_2 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenating_numbers_dp_safety_wit_3 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |-> (signed_last_nbits ((Z.shiftl 1 count_pre)) (32)))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_dp_safety_wit_4 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |-> (signed_last_nbits ((Z.shiftl 1 count_pre)) (32)))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition concatenating_numbers_dp_safety_wit_5 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "state_count" ) )) # Int  |-> (signed_last_nbits ((Z.shiftl 1 count_pre)) (32)))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenating_numbers_dp_safety_wit_6 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  ((( &( "mask" ) )) # Int  |->_)
  **  (((best_first_pre + (0 * sizeof(INT)))) # Int  |-> (-1))
  **  (IntArray.undef_seg best_first_pre 1 (Z.shiftl (1) (count_pre)) )
  **  ((( &( "state_count" ) )) # Int  |-> (signed_last_nbits ((Z.shiftl 1 count_pre)) (32)))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenating_numbers_dp_safety_wit_7 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask < state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices )) ,
  ((( &( "bit" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_dp_safety_wit_8 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask < state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices )) ,
  ((( &( "bit_value" ) )) # Int  |->_)
  **  ((( &( "bit" ) )) # Int  |-> 0)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenating_numbers_dp_safety_wit_9 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : (0 <= bit)) (PreH11 : (bit <= count_pre)) (PreH12 : (1 <= bit_value)) (PreH13 : (bit_value <= state_count)) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = mask)) (PreH17 : (DPTablePrefix rows lens count_pre mask choices )) (PreH18 : (BitScanState mask count_pre bit bit_value )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_dp_safety_wit_10 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((bit + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (bit + 1 )) ”
.

Definition concatenating_numbers_dp_safety_wit_11 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> (bit + 1 ))
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((signed_last_nbits ((bit_value * (2^1) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((bit_value * (2^1) )) (32))) ” 
  &&  “ (1 <= 31) ” 
  &&  “ (0 <= 1) ”
) \/
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> (bit + 1 ))
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((signed_last_nbits ((bit_value * (2^1) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((bit_value * (2^1) )) (32))) ” 
  &&  “ (1 <= 31) ” 
  &&  “ (0 <= 1) ”
).

Definition concatenating_numbers_dp_safety_wit_11_split_goal_1 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> (bit + 1 ))
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((signed_last_nbits ((bit_value * (2^1) )) (32)) <= INT_MAX) ”
.

Definition concatenating_numbers_dp_safety_wit_11_split_goal_2 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> (bit + 1 ))
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((bit_value * (2^1) )) (32))) ”
.

Definition concatenating_numbers_dp_safety_wit_11_split_goal_3 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> (bit + 1 ))
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= 31) ”
.

Definition concatenating_numbers_dp_safety_wit_11_split_goal_4 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> (bit + 1 ))
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= 1) ”
.

Definition concatenating_numbers_dp_safety_wit_12 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> (bit + 1 ))
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenating_numbers_dp_safety_wit_13 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : (0 <= bit)) (PreH11 : (bit < count_pre)) (PreH12 : (0 <= rest)) (PreH13 : (rest < mask)) (PreH14 : ((Zlength (choices)) = mask)) (PreH15 : (previous_best = (Znth (rest) (choices) (0)))) (PreH16 : (rest = 0)) (PreH17 : (previous_best = (-1))) (PreH18 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH19 : (FlatRows flat rows count_pre number_width_pre )) (PreH20 : (DPTablePrefix rows lens count_pre mask choices )) (PreH21 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "rest" ) )) # Int  |-> rest)
  **  ((( &( "previous_best" ) )) # Int  |-> previous_best)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_dp_safety_wit_14 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : (0 <= bit)) (PreH11 : (bit < count_pre)) (PreH12 : (0 <= rest)) (PreH13 : (rest < mask)) (PreH14 : ((Zlength (choices)) = mask)) (PreH15 : (previous_best = (Znth (rest) (choices) (0)))) (PreH16 : (1 <= rest)) (PreH17 : (0 <= previous_best)) (PreH18 : (previous_best < count_pre)) (PreH19 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH20 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH21 : (FlatRows flat rows count_pre number_width_pre )) (PreH22 : (DPTablePrefix rows lens count_pre mask choices )) (PreH23 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "rest" ) )) # Int  |-> rest)
  **  ((( &( "previous_best" ) )) # Int  |-> previous_best)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_dp_safety_wit_15 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (previous_best >= 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : (0 <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices) (0)))) (PreH17 : (rest = 0)) (PreH18 : (previous_best = (-1))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) (PreH21 : (DPTablePrefix rows lens count_pre mask choices )) (PreH22 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "rest" ) )) # Int  |-> rest)
  **  ((( &( "previous_best" ) )) # Int  |-> previous_best)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ False ”
.

Definition concatenating_numbers_dp_safety_wit_16 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (previous_best < 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : (0 <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices) (0)))) (PreH17 : (1 <= rest)) (PreH18 : (0 <= previous_best)) (PreH19 : (previous_best < count_pre)) (PreH20 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH21 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH22 : (FlatRows flat rows count_pre number_width_pre )) (PreH23 : (DPTablePrefix rows lens count_pre mask choices )) (PreH24 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "rest" ) )) # Int  |-> rest)
  **  ((( &( "previous_best" ) )) # Int  |-> previous_best)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ False ”
.

Definition concatenating_numbers_dp_safety_wit_17 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH2 : (previous_best >= 0)) (PreH3 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH4 : (1 <= count_pre)) (PreH5 : (count_pre <= 20)) (PreH6 : (1 <= number_width_pre)) (PreH7 : (number_width_pre <= 10)) (PreH8 : (1 <= (sum (lens)))) (PreH9 : ((sum (lens)) <= 200)) (PreH10 : (1 <= mask)) (PreH11 : (mask < state_count)) (PreH12 : (0 <= bit)) (PreH13 : (bit < count_pre)) (PreH14 : (0 <= rest)) (PreH15 : (rest < mask)) (PreH16 : ((Zlength (choices)) = mask)) (PreH17 : (previous_best = (Znth (rest) (choices) (0)))) (PreH18 : (1 <= rest)) (PreH19 : (0 <= previous_best)) (PreH20 : (previous_best < count_pre)) (PreH21 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre mask choices )) (PreH25 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "rest" ) )) # Int  |-> rest)
  **  ((( &( "previous_best" ) )) # Int  |-> previous_best)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_dp_safety_wit_18 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH11 : (FlatRows flat rows count_pre number_width_pre )) (PreH12 : ((Zlength (choices)) = (mask + 1 ))) (PreH13 : (DPTablePrefix rows lens count_pre (mask + 1 ) choices )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 (mask + 1 ) choices )
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((mask + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (mask + 1 )) ”
.

Definition concatenating_numbers_dp_safety_wit_19 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask >= state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices )) ,
  ((( &( "mask" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ ((state_count - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (state_count - 1 )) ”
.

Definition concatenating_numbers_dp_safety_wit_20 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask >= state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices )) ,
  ((( &( "mask" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenating_numbers_dp_safety_wit_21 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask >= state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices )) ,
  ((( &( "result_length" ) )) # Int  |->_)
  **  ((( &( "mask" ) )) # Int  |-> (state_count - 1 ))
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_dp_safety_wit_22 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (0 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : (result_length = (Zlength (output)))) (PreH11 : (0 <= result_length)) (PreH12 : (result_length <= (sum (lens)))) (PreH13 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH14 : (FlatRows flat rows count_pre number_width_pre )) (PreH15 : ((Zlength (choices)) = state_count)) (PreH16 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH17 : (GreedyOutputPrefix rows lens count_pre mask output )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_dp_safety_wit_23 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output: (@list Z)) (state_count: Z) (mask: Z) (first: Z) (result_length: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : ((Zlength (choices)) = state_count)) (PreH11 : (first = (Znth (mask) (choices) (0)))) (PreH12 : (0 <= first)) (PreH13 : (first < count_pre)) (PreH14 : (1 <= (Znth (first) (lens) (0)))) (PreH15 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH16 : (result_length = (Zlength (output)))) (PreH17 : (0 <= result_length)) (PreH18 : ((result_length + (Znth (first) (lens) (0)) ) <= (sum (lens)))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) (PreH21 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH22 : (BestIndexForMask rows lens count_pre mask first )) (PreH23 : (GreedyOutputPrefix rows lens count_pre mask output )) ,
  ((( &( "position" ) )) # Int  |->_)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition concatenating_numbers_dp_safety_wit_24 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (0 <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (position <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (first <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (position >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (0 <= ((first * number_width_pre ) + position ))) (PreH12 : (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (mask <= INT_MAX)) (PreH15 : (state_count <= INT_MAX)) (PreH16 : (result_length >= INT_MIN)) (PreH17 : (mask >= INT_MIN)) (PreH18 : (state_count >= INT_MIN)) (PreH19 : (position < (Znth first lens 0))) (PreH20 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (1 <= mask)) (PreH28 : (mask < state_count)) (PreH29 : ((Zlength (choices)) = state_count)) (PreH30 : (first = (Znth (mask) (choices) (0)))) (PreH31 : (0 <= first)) (PreH32 : (first < count_pre)) (PreH33 : (0 <= position)) (PreH34 : (position <= (Znth (first) (lens) (0)))) (PreH35 : (1 <= (Znth (first) (lens) (0)))) (PreH36 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH37 : (result_length = (Zlength (output)))) (PreH38 : (0 <= result_length)) (PreH39 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH40 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH41 : (FlatRows flat rows count_pre number_width_pre )) (PreH42 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH43 : (BestIndexForMask rows lens count_pre mask first )) (PreH44 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH45 : (AppendRowPrefix rows lens prior first position output )) ,
  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (((first * number_width_pre ) + position ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((first * number_width_pre ) + position )) ”
.

Definition concatenating_numbers_dp_safety_wit_25 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (0 <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (position <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (first <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (position >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (0 <= ((first * number_width_pre ) + position ))) (PreH12 : (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (mask <= INT_MAX)) (PreH15 : (state_count <= INT_MAX)) (PreH16 : (result_length >= INT_MIN)) (PreH17 : (mask >= INT_MIN)) (PreH18 : (state_count >= INT_MIN)) (PreH19 : (position < (Znth first lens 0))) (PreH20 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (1 <= mask)) (PreH28 : (mask < state_count)) (PreH29 : ((Zlength (choices)) = state_count)) (PreH30 : (first = (Znth (mask) (choices) (0)))) (PreH31 : (0 <= first)) (PreH32 : (first < count_pre)) (PreH33 : (0 <= position)) (PreH34 : (position <= (Znth (first) (lens) (0)))) (PreH35 : (1 <= (Znth (first) (lens) (0)))) (PreH36 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH37 : (result_length = (Zlength (output)))) (PreH38 : (0 <= result_length)) (PreH39 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH40 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH41 : (FlatRows flat rows count_pre number_width_pre )) (PreH42 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH43 : (BestIndexForMask rows lens count_pre mask first )) (PreH44 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH45 : (AppendRowPrefix rows lens prior first position output )) ,
  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ ((first * number_width_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (first * number_width_pre )) ”
.

Definition concatenating_numbers_dp_safety_wit_26 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (0 <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (position <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (first <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (position >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (0 <= ((first * number_width_pre ) + position ))) (PreH12 : (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (mask <= INT_MAX)) (PreH15 : (state_count <= INT_MAX)) (PreH16 : (result_length >= INT_MIN)) (PreH17 : (mask >= INT_MIN)) (PreH18 : (state_count >= INT_MIN)) (PreH19 : (position < (Znth first lens 0))) (PreH20 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (1 <= mask)) (PreH28 : (mask < state_count)) (PreH29 : ((Zlength (choices)) = state_count)) (PreH30 : (first = (Znth (mask) (choices) (0)))) (PreH31 : (0 <= first)) (PreH32 : (first < count_pre)) (PreH33 : (0 <= position)) (PreH34 : (position <= (Znth (first) (lens) (0)))) (PreH35 : (1 <= (Znth (first) (lens) (0)))) (PreH36 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH37 : (result_length = (Zlength (output)))) (PreH38 : (0 <= result_length)) (PreH39 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH40 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH41 : (FlatRows flat rows count_pre number_width_pre )) (PreH42 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH43 : (BestIndexForMask rows lens count_pre mask first )) (PreH44 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH45 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.seg result_pre 0 (result_length + 1 ) (app (output) ((cons ((Znth ((first * number_width_pre ) + position ) flat 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full best_first_pre state_count choices )
|--
  “ ((result_length + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result_length + 1 )) ”
.

Definition concatenating_numbers_dp_safety_wit_27 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (0 <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (position <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (first <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (position >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (0 <= ((first * number_width_pre ) + position ))) (PreH12 : (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (mask <= INT_MAX)) (PreH15 : (state_count <= INT_MAX)) (PreH16 : (result_length >= INT_MIN)) (PreH17 : (mask >= INT_MIN)) (PreH18 : (state_count >= INT_MIN)) (PreH19 : (position < (Znth first lens 0))) (PreH20 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (1 <= mask)) (PreH28 : (mask < state_count)) (PreH29 : ((Zlength (choices)) = state_count)) (PreH30 : (first = (Znth (mask) (choices) (0)))) (PreH31 : (0 <= first)) (PreH32 : (first < count_pre)) (PreH33 : (0 <= position)) (PreH34 : (position <= (Znth (first) (lens) (0)))) (PreH35 : (1 <= (Znth (first) (lens) (0)))) (PreH36 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH37 : (result_length = (Zlength (output)))) (PreH38 : (0 <= result_length)) (PreH39 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH40 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH41 : (FlatRows flat rows count_pre number_width_pre )) (PreH42 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH43 : (BestIndexForMask rows lens count_pre mask first )) (PreH44 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH45 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.seg result_pre 0 (result_length + 1 ) (app (output) ((cons ((Znth ((first * number_width_pre ) + position ) flat 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  ((( &( "result_length" ) )) # Int  |-> (result_length + 1 ))
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full best_first_pre state_count choices )
|--
  “ ((position + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (position + 1 )) ”
.

Definition concatenating_numbers_dp_safety_wit_28 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices)) = state_count)) (PreH12 : (first = (Znth (mask) (choices) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ ((signed_last_nbits ((1 * (2^first) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^first) )) (32))) ” 
  &&  “ (first <= 31) ” 
  &&  “ (0 <= first) ”
) \/
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices)) = state_count)) (PreH12 : (first = (Znth (mask) (choices) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ ((signed_last_nbits ((1 * (2^first) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^first) )) (32))) ” 
  &&  “ (first <= 31) ” 
  &&  “ (0 <= first) ”
).

Definition concatenating_numbers_dp_safety_wit_28_split_goal_1 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices)) = state_count)) (PreH12 : (first = (Znth (mask) (choices) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ ((signed_last_nbits ((1 * (2^first) )) (32)) <= INT_MAX) ”
.

Definition concatenating_numbers_dp_safety_wit_28_split_goal_2 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices)) = state_count)) (PreH12 : (first = (Znth (mask) (choices) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^first) )) (32))) ”
.

Definition concatenating_numbers_dp_safety_wit_28_split_goal_3 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices)) = state_count)) (PreH12 : (first = (Znth (mask) (choices) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (first <= 31) ”
.

Definition concatenating_numbers_dp_safety_wit_28_split_goal_4 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices)) = state_count)) (PreH12 : (first = (Znth (mask) (choices) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (0 <= first) ”
.

Definition concatenating_numbers_dp_safety_wit_29 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices)) = state_count)) (PreH12 : (first = (Znth (mask) (choices) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition concatenating_numbers_dp_entail_wit_1 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  (((best_first_pre + (0 * sizeof(INT)))) # Int  |-> (-1))
  **  (IntArray.undef_seg best_first_pre 1 (Z.shiftl (1) (count_pre)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (choices: (@list Z)) ,
  “ ((signed_last_nbits ((Z.shiftl 1 count_pre)) (32)) = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (signed_last_nbits ((Z.shiftl 1 count_pre)) (32))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = 1) ” 
  &&  “ (DPTablePrefix rows lens count_pre 1 choices ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 1 choices )
  **  (IntArray.undef_seg best_first_pre 1 (signed_last_nbits ((Z.shiftl 1 count_pre)) (32)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
) \/
(
forall (best_first_pre: Z) (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : ((-1) <= INT_MAX)) (PreH2 : ((-1) >= INT_MIN)) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH8 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) ,
  (((best_first_pre + (0 * sizeof(INT)))) # Int  |-> (-1))
  **  (IntArray.undef_seg best_first_pre 1 (Z.shiftl (1) (count_pre)) )
|--
  EX (choices: (@list Z)) ,
  “ ((signed_last_nbits ((Z.shiftl 1 count_pre)) (32)) = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (signed_last_nbits ((Z.shiftl 1 count_pre)) (32))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = 1) ” 
  &&  “ (DPTablePrefix rows lens count_pre 1 choices ) ”
  &&  (IntArray.seg best_first_pre 0 1 choices )
  **  (IntArray.undef_seg best_first_pre 1 (signed_last_nbits ((Z.shiftl 1 count_pre)) (32)) )
).

Definition concatenating_numbers_dp_entail_wit_2 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask < state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices_2)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices_2 )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices_2 )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= count_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= state_count) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = mask) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices ) ” 
  &&  “ (BitScanState mask count_pre 0 1 ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask < state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices_2)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices_2 )) ,
  TT && emp 
|--
  “ (BitScanState mask count_pre 0 1 ) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_2_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask < state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices_2)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices_2 )) ,
  (BitScanState mask count_pre 0 1 )
.

Definition concatenating_numbers_dp_entail_wit_3 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices_2 )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= (bit + 1 )) ” 
  &&  “ ((bit + 1 ) <= count_pre) ” 
  &&  “ (1 <= (signed_last_nbits ((Z.shiftl bit_value 1)) (32))) ” 
  &&  “ ((signed_last_nbits ((Z.shiftl bit_value 1)) (32)) <= state_count) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = mask) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices ) ” 
  &&  “ (BitScanState mask count_pre (bit + 1 ) (signed_last_nbits ((Z.shiftl bit_value 1)) (32)) ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  TT && emp 
|--
  “ (BitScanState mask count_pre (bit + 1 ) (signed_last_nbits ((Z.shiftl bit_value 1)) (32)) ) ” 
  &&  “ ((signed_last_nbits ((Z.shiftl bit_value 1)) (32)) <= state_count) ” 
  &&  “ (1 <= (signed_last_nbits ((Z.shiftl bit_value 1)) (32))) ” 
  &&  “ ((bit + 1 ) <= count_pre) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_3_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  (BitScanState mask count_pre (bit + 1 ) (signed_last_nbits ((Z.shiftl bit_value 1)) (32)) )
.

Definition concatenating_numbers_dp_entail_wit_3_split_goal_2 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((signed_last_nbits ((Z.shiftl bit_value 1)) (32)) <= state_count)
.

Definition concatenating_numbers_dp_entail_wit_3_split_goal_3 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  (1 <= (signed_last_nbits ((Z.shiftl bit_value 1)) (32)))
.

Definition concatenating_numbers_dp_entail_wit_3_split_goal_4 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((bit + 1 ) <= count_pre)
.

Definition concatenating_numbers_dp_entail_wit_4 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices_2 )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (1 <= bit_value) ” 
  &&  “ (bit_value < state_count) ” 
  &&  “ (0 <= (Z.lxor mask bit_value)) ” 
  &&  “ ((Z.lxor mask bit_value) < mask) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = mask) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices ) ” 
  &&  “ (SelectedBitState mask count_pre bit bit_value (Z.lxor mask bit_value) ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  TT && emp 
|--
  “ (SelectedBitState mask count_pre bit bit_value (Z.lxor mask bit_value) ) ” 
  &&  “ ((Z.lxor mask bit_value) < mask) ” 
  &&  “ (0 <= (Z.lxor mask bit_value)) ” 
  &&  “ (bit_value < state_count) ” 
  &&  “ (bit < count_pre) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_4_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  (SelectedBitState mask count_pre bit bit_value (Z.lxor mask bit_value) )
.

Definition concatenating_numbers_dp_entail_wit_4_split_goal_2 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  ((Z.lxor mask bit_value) < mask)
.

Definition concatenating_numbers_dp_entail_wit_4_split_goal_3 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  (0 <= (Z.lxor mask bit_value))
.

Definition concatenating_numbers_dp_entail_wit_4_split_goal_4 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  (bit_value < state_count)
.

Definition concatenating_numbers_dp_entail_wit_4_split_goal_5 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (bit_value: Z) (bit: Z) (mask: Z) (state_count: Z) (PreH1 : ((Z.land mask bit_value) <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit <= count_pre)) (PreH13 : (1 <= bit_value)) (PreH14 : (bit_value <= state_count)) (PreH15 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH16 : (FlatRows flat rows count_pre number_width_pre )) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH19 : (BitScanState mask count_pre bit bit_value )) ,
  (bit < count_pre)
.

Definition concatenating_numbers_dp_entail_wit_5 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (bit_value: Z) (rest: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : (0 <= bit)) (PreH11 : (bit < count_pre)) (PreH12 : (1 <= bit_value)) (PreH13 : (bit_value < state_count)) (PreH14 : (0 <= rest)) (PreH15 : (rest < mask)) (PreH16 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) (PreH18 : ((Zlength (choices)) = mask)) (PreH19 : (DPTablePrefix rows lens count_pre mask choices )) (PreH20 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  (EX (choices_2: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (0 <= rest) ” 
  &&  “ (rest < mask) ” 
  &&  “ ((Zlength (choices_2)) = mask) ” 
  &&  “ ((Znth (rest - 0 ) choices 0) = (Znth (rest) (choices_2) (0))) ” 
  &&  “ (rest = 0) ” 
  &&  “ ((Znth (rest - 0 ) choices 0) = (-1)) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices_2 ) ” 
  &&  “ (SelectedBitState mask count_pre bit bit_value rest ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices_2 )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) ))
  ||
  (EX (choices_3: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (0 <= rest) ” 
  &&  “ (rest < mask) ” 
  &&  “ ((Zlength (choices_3)) = mask) ” 
  &&  “ ((Znth (rest - 0 ) choices 0) = (Znth (rest) (choices_3) (0))) ” 
  &&  “ (1 <= rest) ” 
  &&  “ (0 <= (Znth (rest - 0 ) choices 0)) ” 
  &&  “ ((Znth (rest - 0 ) choices 0) < count_pre) ” 
  &&  “ (BestIndexForMask rows lens count_pre rest (Znth (rest - 0 ) choices 0) ) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices_3 ) ” 
  &&  “ (SelectedBitState mask count_pre bit bit_value rest ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices_3 )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) ))
.

Definition concatenating_numbers_dp_entail_wit_6_1 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (previous_best < 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : (0 <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices_2)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH17 : (rest = 0)) (PreH18 : (previous_best = (-1))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) (PreH21 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH22 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.seg best_first_pre 0 (mask + 1 ) (app (choices_2) ((cons (bit) ((@nil Z))))) )
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "rest" ) )) # Int  |-> rest)
  **  ((( &( "previous_best" ) )) # Int  |-> previous_best)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = (mask + 1 )) ” 
  &&  “ (DPTablePrefix rows lens count_pre (mask + 1 ) choices ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 (mask + 1 ) choices )
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
  **  ((( &( "bit" ) )) # Int  |->_)
  **  ((( &( "bit_value" ) )) # Int  |->_)
  **  ((( &( "rest" ) )) # Int  |->_)
  **  ((( &( "previous_best" ) )) # Int  |->_)
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (previous_best < 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : (0 <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices_2)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH17 : (rest = 0)) (PreH18 : (previous_best = (-1))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) (PreH21 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH22 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  TT && emp 
|--
  “ (DPTablePrefix rows lens count_pre (mask + 1 ) (app (choices_2) ((cons (bit) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (choices_2) ((cons (bit) ((@nil Z))))))) = (mask + 1 )) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_6_1_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (previous_best < 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : (0 <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices_2)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH17 : (rest = 0)) (PreH18 : (previous_best = (-1))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) (PreH21 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH22 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (DPTablePrefix rows lens count_pre (mask + 1 ) (app (choices_2) ((cons (bit) ((@nil Z))))) )
.

Definition concatenating_numbers_dp_entail_wit_6_1_split_goal_2 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (previous_best < 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : (0 <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices_2)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH17 : (rest = 0)) (PreH18 : (previous_best = (-1))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) (PreH21 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH22 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  ((Zlength ((app (choices_2) ((cons (bit) ((@nil Z))))))) = (mask + 1 ))
.

Definition concatenating_numbers_dp_entail_wit_6_2 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.seg best_first_pre 0 (mask + 1 ) (app (choices_2) ((cons (bit) ((@nil Z))))) )
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "rest" ) )) # Int  |-> rest)
  **  ((( &( "previous_best" ) )) # Int  |-> previous_best)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = (mask + 1 )) ” 
  &&  “ (DPTablePrefix rows lens count_pre (mask + 1 ) choices ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 (mask + 1 ) choices )
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
  **  ((( &( "bit" ) )) # Int  |->_)
  **  ((( &( "bit_value" ) )) # Int  |->_)
  **  ((( &( "rest" ) )) # Int  |->_)
  **  ((( &( "previous_best" ) )) # Int  |->_)
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  TT && emp 
|--
  “ (DPTablePrefix rows lens count_pre (mask + 1 ) (app (choices_2) ((cons (bit) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (choices_2) ((cons (bit) ((@nil Z))))))) = (mask + 1 )) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_6_2_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (DPTablePrefix rows lens count_pre (mask + 1 ) (app (choices_2) ((cons (bit) ((@nil Z))))) )
.

Definition concatenating_numbers_dp_entail_wit_6_2_split_goal_2 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  ((Zlength ((app (choices_2) ((cons (bit) ((@nil Z))))))) = (mask + 1 ))
.

Definition concatenating_numbers_dp_entail_wit_6_3 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.seg best_first_pre 0 (mask + 1 ) (app (choices_2) ((cons (previous_best) ((@nil Z))))) )
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "rest" ) )) # Int  |-> rest)
  **  ((( &( "previous_best" ) )) # Int  |-> previous_best)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = (mask + 1 )) ” 
  &&  “ (DPTablePrefix rows lens count_pre (mask + 1 ) choices ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 (mask + 1 ) choices )
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
  **  ((( &( "bit" ) )) # Int  |->_)
  **  ((( &( "bit_value" ) )) # Int  |->_)
  **  ((( &( "rest" ) )) # Int  |->_)
  **  ((( &( "previous_best" ) )) # Int  |->_)
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  TT && emp 
|--
  “ (DPTablePrefix rows lens count_pre (mask + 1 ) (app (choices_2) ((cons (previous_best) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (choices_2) ((cons (previous_best) ((@nil Z))))))) = (mask + 1 )) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_6_3_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (DPTablePrefix rows lens count_pre (mask + 1 ) (app (choices_2) ((cons (previous_best) ((@nil Z))))) )
.

Definition concatenating_numbers_dp_entail_wit_6_3_split_goal_2 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices_2)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices_2) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices_2 )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  ((Zlength ((app (choices_2) ((cons (previous_best) ((@nil Z))))))) = (mask + 1 ))
.

Definition concatenating_numbers_dp_entail_wit_7 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (state_count: Z) (mask: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH11 : (FlatRows flat rows count_pre number_width_pre )) (PreH12 : ((Zlength (choices_2)) = (mask + 1 ))) (PreH13 : (DPTablePrefix rows lens count_pre (mask + 1 ) choices_2 )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 (mask + 1 ) choices_2 )
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= (mask + 1 )) ” 
  &&  “ ((mask + 1 ) <= state_count) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = (mask + 1 )) ” 
  &&  “ (DPTablePrefix rows lens count_pre (mask + 1 ) choices ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 (mask + 1 ) choices )
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
.

Definition concatenating_numbers_dp_entail_wit_8 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask >= state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices_2)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices_2 )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices_2 )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  EX (choices: (@list Z))  (output: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= (state_count - 1 )) ” 
  &&  “ ((state_count - 1 ) < state_count) ” 
  &&  “ (0 = (Zlength (output))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre (state_count - 1 ) output ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 0 output )
  **  (IntArray.undef_seg result_pre 0 (sum (lens)) )
) \/
(
forall (best_first_pre: Z) (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (mask >= state_count)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask <= state_count)) (PreH11 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH12 : (FlatRows flat rows count_pre number_width_pre )) (PreH13 : ((Zlength (choices_2)) = mask)) (PreH14 : (DPTablePrefix rows lens count_pre mask choices_2 )) ,
  (IntArray.seg best_first_pre 0 mask choices_2 )
|--
  EX (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= (state_count - 1 )) ” 
  &&  “ ((state_count - 1 ) < state_count) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre (state_count - 1 ) (@nil Z) ) ”
  &&  (IntArray.full best_first_pre state_count choices )
).

Definition concatenating_numbers_dp_entail_wit_9 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg result_pre 0 result_length output_2 )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  EX (output: (@list Z))  (choices_2: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ ((Zlength (choices_2)) = state_count) ” 
  &&  “ ((Znth mask choices 0) = (Znth (mask) (choices_2) (0))) ” 
  &&  “ (0 <= (Znth mask choices 0)) ” 
  &&  “ ((Znth mask choices 0) < count_pre) ” 
  &&  “ (1 <= (Znth ((Znth mask choices 0)) (lens) (0))) ” 
  &&  “ ((Znth ((Znth mask choices 0)) (lens) (0)) <= number_width_pre) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ ((result_length + (Znth ((Znth mask choices 0)) (lens) (0)) ) <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices_2 ) ” 
  &&  “ (BestIndexForMask rows lens count_pre mask (Znth mask choices 0) ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask output ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices_2 )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  TT && emp 
|--
  “ (BestIndexForMask rows lens count_pre mask (Znth mask choices 0) ) ” 
  &&  “ ((result_length + (Znth ((Znth mask choices 0)) (lens) (0)) ) <= (sum (lens))) ” 
  &&  “ ((Znth ((Znth mask choices 0)) (lens) (0)) <= number_width_pre) ” 
  &&  “ (1 <= (Znth ((Znth mask choices 0)) (lens) (0))) ” 
  &&  “ ((Znth mask choices 0) < count_pre) ” 
  &&  “ (0 <= (Znth mask choices 0)) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_9_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  (BestIndexForMask rows lens count_pre mask (Znth mask choices 0) )
.

Definition concatenating_numbers_dp_entail_wit_9_split_goal_2 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  ((result_length + (Znth ((Znth mask choices 0)) (lens) (0)) ) <= (sum (lens)))
.

Definition concatenating_numbers_dp_entail_wit_9_split_goal_3 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  ((Znth ((Znth mask choices 0)) (lens) (0)) <= number_width_pre)
.

Definition concatenating_numbers_dp_entail_wit_9_split_goal_4 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  (1 <= (Znth ((Znth mask choices 0)) (lens) (0)))
.

Definition concatenating_numbers_dp_entail_wit_9_split_goal_5 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  ((Znth mask choices 0) < count_pre)
.

Definition concatenating_numbers_dp_entail_wit_9_split_goal_6 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  (0 <= (Znth mask choices 0))
.

Definition concatenating_numbers_dp_entail_wit_10 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (output_2: (@list Z)) (state_count: Z) (mask: Z) (first: Z) (result_length: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : ((Zlength (choices_2)) = state_count)) (PreH11 : (first = (Znth (mask) (choices_2) (0)))) (PreH12 : (0 <= first)) (PreH13 : (first < count_pre)) (PreH14 : (1 <= (Znth (first) (lens) (0)))) (PreH15 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH16 : (result_length = (Zlength (output_2)))) (PreH17 : (0 <= result_length)) (PreH18 : ((result_length + (Znth (first) (lens) (0)) ) <= (sum (lens)))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) (PreH21 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH22 : (BestIndexForMask rows lens count_pre mask first )) (PreH23 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices_2 )
  **  (IntArray.seg result_pre 0 result_length output_2 )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  EX (prior: (@list Z))  (output: (@list Z))  (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (first = (Znth (mask) (choices) (0))) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < count_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (Znth (first) (lens) (0))) ” 
  &&  “ (1 <= (Znth (first) (lens) (0))) ” 
  &&  “ ((Znth (first) (lens) (0)) <= number_width_pre) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ ((result_length + ((Znth (first) (lens) (0)) - 0 ) ) <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (BestIndexForMask rows lens count_pre mask first ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask prior ) ” 
  &&  “ (AppendRowPrefix rows lens prior first 0 output ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (output_2: (@list Z)) (state_count: Z) (mask: Z) (first: Z) (result_length: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : ((Zlength (choices_2)) = state_count)) (PreH11 : (first = (Znth (mask) (choices_2) (0)))) (PreH12 : (0 <= first)) (PreH13 : (first < count_pre)) (PreH14 : (1 <= (Znth (first) (lens) (0)))) (PreH15 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH16 : (result_length = (Zlength (output_2)))) (PreH17 : (0 <= result_length)) (PreH18 : ((result_length + (Znth (first) (lens) (0)) ) <= (sum (lens)))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) (PreH21 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH22 : (BestIndexForMask rows lens count_pre mask first )) (PreH23 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  TT && emp 
|--
  EX (prior: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (Znth ((Znth (mask) (choices_2) (0))) (lens) (0))) ” 
  &&  “ (((Zlength (output_2)) + ((Znth ((Znth (mask) (choices_2) (0))) (lens) (0)) - 0 ) ) <= (sum (lens))) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask prior ) ” 
  &&  “ (AppendRowPrefix rows lens prior (Znth (mask) (choices_2) (0)) 0 output_2 ) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_11 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position < (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices)) = state_count)) (PreH12 : (first = (Znth (mask) (choices) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (0 <= ((first * number_width_pre ) + position )) ” 
  &&  “ (((first * number_width_pre ) + position ) < (count_pre * number_width_pre )) ” 
  &&  “ (result_length <= INT_MAX) ” 
  &&  “ (mask <= INT_MAX) ” 
  &&  “ (state_count <= INT_MAX) ” 
  &&  “ (result_length >= INT_MIN) ” 
  &&  “ (mask >= INT_MIN) ” 
  &&  “ (state_count >= INT_MIN) ” 
  &&  “ (position < (Znth first lens 0)) ” 
  &&  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (first = (Znth (mask) (choices) (0))) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < count_pre) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= (Znth (first) (lens) (0))) ” 
  &&  “ (1 <= (Znth (first) (lens) (0))) ” 
  &&  “ ((Znth (first) (lens) (0)) <= number_width_pre) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (BestIndexForMask rows lens count_pre mask first ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask prior ) ” 
  &&  “ (AppendRowPrefix rows lens prior first position output ) ”
  &&  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (result_length <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (first <= INT_MAX)) (PreH4 : (mask <= INT_MAX)) (PreH5 : (state_count <= INT_MAX)) (PreH6 : (number_width_pre <= INT_MAX)) (PreH7 : (count_pre <= INT_MAX)) (PreH8 : (result_length >= INT_MIN)) (PreH9 : (position >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (mask >= INT_MIN)) (PreH12 : (state_count >= INT_MIN)) (PreH13 : (number_width_pre >= INT_MIN)) (PreH14 : (count_pre >= INT_MIN)) (PreH15 : (position < (Znth first lens 0))) (PreH16 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH17 : (1 <= count_pre)) (PreH18 : (count_pre <= 20)) (PreH19 : (1 <= number_width_pre)) (PreH20 : (number_width_pre <= 10)) (PreH21 : (1 <= (sum (lens)))) (PreH22 : ((sum (lens)) <= 200)) (PreH23 : (1 <= mask)) (PreH24 : (mask < state_count)) (PreH25 : ((Zlength (choices)) = state_count)) (PreH26 : (first = (Znth (mask) (choices) (0)))) (PreH27 : (0 <= first)) (PreH28 : (first < count_pre)) (PreH29 : (0 <= position)) (PreH30 : (position <= (Znth (first) (lens) (0)))) (PreH31 : (1 <= (Znth (first) (lens) (0)))) (PreH32 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH33 : (result_length = (Zlength (output)))) (PreH34 : (0 <= result_length)) (PreH35 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH36 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH37 : (FlatRows flat rows count_pre number_width_pre )) (PreH38 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH39 : (BestIndexForMask rows lens count_pre mask first )) (PreH40 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH41 : (AppendRowPrefix rows lens prior first position output )) ,
  TT && emp 
|--
  “ (((first * number_width_pre ) + position ) < (count_pre * number_width_pre )) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_11_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (result_length <= INT_MAX)) (PreH2 : (position <= INT_MAX)) (PreH3 : (first <= INT_MAX)) (PreH4 : (mask <= INT_MAX)) (PreH5 : (state_count <= INT_MAX)) (PreH6 : (number_width_pre <= INT_MAX)) (PreH7 : (count_pre <= INT_MAX)) (PreH8 : (result_length >= INT_MIN)) (PreH9 : (position >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (mask >= INT_MIN)) (PreH12 : (state_count >= INT_MIN)) (PreH13 : (number_width_pre >= INT_MIN)) (PreH14 : (count_pre >= INT_MIN)) (PreH15 : (position < (Znth first lens 0))) (PreH16 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH17 : (1 <= count_pre)) (PreH18 : (count_pre <= 20)) (PreH19 : (1 <= number_width_pre)) (PreH20 : (number_width_pre <= 10)) (PreH21 : (1 <= (sum (lens)))) (PreH22 : ((sum (lens)) <= 200)) (PreH23 : (1 <= mask)) (PreH24 : (mask < state_count)) (PreH25 : ((Zlength (choices)) = state_count)) (PreH26 : (first = (Znth (mask) (choices) (0)))) (PreH27 : (0 <= first)) (PreH28 : (first < count_pre)) (PreH29 : (0 <= position)) (PreH30 : (position <= (Znth (first) (lens) (0)))) (PreH31 : (1 <= (Znth (first) (lens) (0)))) (PreH32 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH33 : (result_length = (Zlength (output)))) (PreH34 : (0 <= result_length)) (PreH35 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH36 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH37 : (FlatRows flat rows count_pre number_width_pre )) (PreH38 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH39 : (BestIndexForMask rows lens count_pre mask first )) (PreH40 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH41 : (AppendRowPrefix rows lens prior first position output )) ,
  (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))
.

Definition concatenating_numbers_dp_entail_wit_12 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (0 <= ((first * number_width_pre ) + position ))) (PreH2 : (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))) (PreH3 : (result_length <= INT_MAX)) (PreH4 : (mask <= INT_MAX)) (PreH5 : (state_count <= INT_MAX)) (PreH6 : (result_length >= INT_MIN)) (PreH7 : (mask >= INT_MIN)) (PreH8 : (state_count >= INT_MIN)) (PreH9 : (position < (Znth first lens 0))) (PreH10 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH11 : (1 <= count_pre)) (PreH12 : (count_pre <= 20)) (PreH13 : (1 <= number_width_pre)) (PreH14 : (number_width_pre <= 10)) (PreH15 : (1 <= (sum (lens)))) (PreH16 : ((sum (lens)) <= 200)) (PreH17 : (1 <= mask)) (PreH18 : (mask < state_count)) (PreH19 : ((Zlength (choices)) = state_count)) (PreH20 : (first = (Znth (mask) (choices) (0)))) (PreH21 : (0 <= first)) (PreH22 : (first < count_pre)) (PreH23 : (0 <= position)) (PreH24 : (position <= (Znth (first) (lens) (0)))) (PreH25 : (1 <= (Znth (first) (lens) (0)))) (PreH26 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH27 : (result_length = (Zlength (output)))) (PreH28 : (0 <= result_length)) (PreH29 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH30 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH31 : (FlatRows flat rows count_pre number_width_pre )) (PreH32 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH33 : (BestIndexForMask rows lens count_pre mask first )) (PreH34 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH35 : (AppendRowPrefix rows lens prior first position output )) ,
  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (0 <= result_length) ” 
  &&  “ (result_length < (sum (lens))) ” 
  &&  “ (count_pre <= INT_MAX) ” 
  &&  “ (position <= INT_MAX) ” 
  &&  “ (number_width_pre <= INT_MAX) ” 
  &&  “ (first <= INT_MAX) ” 
  &&  “ (count_pre >= INT_MIN) ” 
  &&  “ (position >= INT_MIN) ” 
  &&  “ (number_width_pre >= INT_MIN) ” 
  &&  “ (first >= INT_MIN) ” 
  &&  “ (0 <= ((first * number_width_pre ) + position )) ” 
  &&  “ (((first * number_width_pre ) + position ) < (count_pre * number_width_pre )) ” 
  &&  “ (result_length <= INT_MAX) ” 
  &&  “ (mask <= INT_MAX) ” 
  &&  “ (state_count <= INT_MAX) ” 
  &&  “ (result_length >= INT_MIN) ” 
  &&  “ (mask >= INT_MIN) ” 
  &&  “ (state_count >= INT_MIN) ” 
  &&  “ (position < (Znth first lens 0)) ” 
  &&  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (first = (Znth (mask) (choices) (0))) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < count_pre) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= (Znth (first) (lens) (0))) ” 
  &&  “ (1 <= (Znth (first) (lens) (0))) ” 
  &&  “ ((Znth (first) (lens) (0)) <= number_width_pre) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (BestIndexForMask rows lens count_pre mask first ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask prior ) ” 
  &&  “ (AppendRowPrefix rows lens prior first position output ) ”
  &&  ((( &( "result_length" ) )) # Int  |-> result_length)
  **  ((( &( "first" ) )) # Int  |-> first)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "position" ) )) # Int  |-> position)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  (IntArray.full lengths_pre count_pre lens )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
.

Definition concatenating_numbers_dp_entail_wit_13 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior_2: (@list Z)) (output_2: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (0 <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (position <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (first <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (position >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (0 <= ((first * number_width_pre ) + position ))) (PreH12 : (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (mask <= INT_MAX)) (PreH15 : (state_count <= INT_MAX)) (PreH16 : (result_length >= INT_MIN)) (PreH17 : (mask >= INT_MIN)) (PreH18 : (state_count >= INT_MIN)) (PreH19 : (position < (Znth first lens 0))) (PreH20 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (1 <= mask)) (PreH28 : (mask < state_count)) (PreH29 : ((Zlength (choices_2)) = state_count)) (PreH30 : (first = (Znth (mask) (choices_2) (0)))) (PreH31 : (0 <= first)) (PreH32 : (first < count_pre)) (PreH33 : (0 <= position)) (PreH34 : (position <= (Znth (first) (lens) (0)))) (PreH35 : (1 <= (Znth (first) (lens) (0)))) (PreH36 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH37 : (result_length = (Zlength (output_2)))) (PreH38 : (0 <= result_length)) (PreH39 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH40 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH41 : (FlatRows flat rows count_pre number_width_pre )) (PreH42 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH43 : (BestIndexForMask rows lens count_pre mask first )) (PreH44 : (GreedyOutputPrefix rows lens count_pre mask prior_2 )) (PreH45 : (AppendRowPrefix rows lens prior_2 first position output_2 )) ,
  (IntArray.seg result_pre 0 (result_length + 1 ) (app (output_2) ((cons ((Znth ((first * number_width_pre ) + position ) flat 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices_2 )
|--
  EX (prior: (@list Z))  (output: (@list Z))  (choices: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (first = (Znth (mask) (choices) (0))) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < count_pre) ” 
  &&  “ (0 <= (position + 1 )) ” 
  &&  “ ((position + 1 ) <= (Znth (first) (lens) (0))) ” 
  &&  “ (1 <= (Znth (first) (lens) (0))) ” 
  &&  “ ((Znth (first) (lens) (0)) <= number_width_pre) ” 
  &&  “ ((result_length + 1 ) = (Zlength (output))) ” 
  &&  “ (0 <= (result_length + 1 )) ” 
  &&  “ (((result_length + 1 ) + ((Znth (first) (lens) (0)) - (position + 1 ) ) ) <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (BestIndexForMask rows lens count_pre mask first ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask prior ) ” 
  &&  “ (AppendRowPrefix rows lens prior first (position + 1 ) output ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 (result_length + 1 ) output )
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior_2: (@list Z)) (output_2: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (0 <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (position <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (first <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (position >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (0 <= ((first * number_width_pre ) + position ))) (PreH12 : (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (mask <= INT_MAX)) (PreH15 : (state_count <= INT_MAX)) (PreH16 : (result_length >= INT_MIN)) (PreH17 : (mask >= INT_MIN)) (PreH18 : (state_count >= INT_MIN)) (PreH19 : (position < (Znth first lens 0))) (PreH20 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (1 <= mask)) (PreH28 : (mask < state_count)) (PreH29 : ((Zlength (choices_2)) = state_count)) (PreH30 : (first = (Znth (mask) (choices_2) (0)))) (PreH31 : (0 <= first)) (PreH32 : (first < count_pre)) (PreH33 : (0 <= position)) (PreH34 : (position <= (Znth (first) (lens) (0)))) (PreH35 : (1 <= (Znth (first) (lens) (0)))) (PreH36 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH37 : (result_length = (Zlength (output_2)))) (PreH38 : (0 <= result_length)) (PreH39 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH40 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH41 : (FlatRows flat rows count_pre number_width_pre )) (PreH42 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH43 : (BestIndexForMask rows lens count_pre mask first )) (PreH44 : (GreedyOutputPrefix rows lens count_pre mask prior_2 )) (PreH45 : (AppendRowPrefix rows lens prior_2 first position output_2 )) ,
  TT && emp 
|--
  EX (prior: (@list Z)) ,
  “ (0 <= (position + 1 )) ” 
  &&  “ ((position + 1 ) <= (Znth ((Znth (mask) (choices_2) (0))) (lens) (0))) ” 
  &&  “ (((Zlength (output_2)) + 1 ) = (Zlength ((app (output_2) ((cons ((Znth (((Znth (mask) (choices_2) (0)) * number_width_pre ) + position ) flat 0)) ((@nil Z)))))))) ” 
  &&  “ (0 <= ((Zlength (output_2)) + 1 )) ” 
  &&  “ ((((Zlength (output_2)) + 1 ) + ((Znth ((Znth (mask) (choices_2) (0))) (lens) (0)) - (position + 1 ) ) ) <= (sum (lens))) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask prior ) ” 
  &&  “ (AppendRowPrefix rows lens prior (Znth (mask) (choices_2) (0)) (position + 1 ) (app (output_2) ((cons ((Znth (((Znth (mask) (choices_2) (0)) * number_width_pre ) + position ) flat 0)) ((@nil Z))))) ) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_14 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output_2: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices_2)) = state_count)) (PreH12 : (first = (Znth (mask) (choices_2) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output_2 )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices_2 )
  **  (IntArray.seg result_pre 0 result_length output_2 )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  EX (choices: (@list Z))  (output: (@list Z)) ,
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= (Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32)))) ” 
  &&  “ ((Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))) < state_count) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ (result_length <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre (Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))) output ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
) \/
(
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output_2: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices_2)) = state_count)) (PreH12 : (first = (Znth (mask) (choices_2) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output_2 )) ,
  TT && emp 
|--
  “ (GreedyOutputPrefix rows lens count_pre (Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))) output_2 ) ” 
  &&  “ ((Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))) < state_count) ” 
  &&  “ (0 <= (Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32)))) ”
  &&  emp
).

Definition concatenating_numbers_dp_entail_wit_14_split_goal_1 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output_2: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices_2)) = state_count)) (PreH12 : (first = (Znth (mask) (choices_2) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output_2 )) ,
  (GreedyOutputPrefix rows lens count_pre (Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))) output_2 )
.

Definition concatenating_numbers_dp_entail_wit_14_split_goal_2 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output_2: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices_2)) = state_count)) (PreH12 : (first = (Znth (mask) (choices_2) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output_2 )) ,
  ((Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))) < state_count)
.

Definition concatenating_numbers_dp_entail_wit_14_split_goal_3 := 
forall (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output_2: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices_2: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (position >= (Znth first lens 0))) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : ((Zlength (choices_2)) = state_count)) (PreH12 : (first = (Znth (mask) (choices_2) (0)))) (PreH13 : (0 <= first)) (PreH14 : (first < count_pre)) (PreH15 : (0 <= position)) (PreH16 : (position <= (Znth (first) (lens) (0)))) (PreH17 : (1 <= (Znth (first) (lens) (0)))) (PreH18 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH19 : (result_length = (Zlength (output_2)))) (PreH20 : (0 <= result_length)) (PreH21 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH22 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH23 : (FlatRows flat rows count_pre number_width_pre )) (PreH24 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH25 : (BestIndexForMask rows lens count_pre mask first )) (PreH26 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH27 : (AppendRowPrefix rows lens prior first position output_2 )) ,
  (0 <= (Z.lxor mask (signed_last_nbits ((Z.shiftl 1 first)) (32))))
.

Definition concatenating_numbers_dp_return_wit_1 := 
(
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices_2)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices_2 )
  **  (IntArray.seg result_pre 0 result_length output_2 )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  EX (output: (@list Z))  (choices: (@list Z)) ,
  “ (result_pre = result_pre) ” 
  &&  “ (DPTablePrefix rows lens count_pre (Z.shiftl (1) (count_pre)) choices ) ” 
  &&  “ (LargestConcatenation rows lens output ) ” 
  &&  “ ((Zlength (output)) = (sum (lens))) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre (Z.shiftl (1) (count_pre)) choices )
  **  (IntArray.full result_pre (sum (lens)) output )
) \/
(
forall (result_pre: Z) (best_first_pre: Z) (number_width_pre: Z) (count_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices_2: (@list Z)) (output_2: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask = 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output_2)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices_2)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices_2 )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output_2 )) ,
  (IntArray.full best_first_pre state_count choices_2 )
  **  (IntArray.seg result_pre 0 result_length output_2 )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  EX (output: (@list Z))  (choices: (@list Z)) ,
  “ (DPTablePrefix rows lens count_pre (Z.shiftl (1) (count_pre)) choices ) ” 
  &&  “ (LargestConcatenation rows lens output ) ” 
  &&  “ ((Zlength (output)) = (sum (lens))) ”
  &&  (IntArray.full best_first_pre (Z.shiftl (1) (count_pre)) choices )
  **  (IntArray.full result_pre (sum (lens)) output )
).

Definition concatenating_numbers_dp_partial_solve_wit_1 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (1 <= count_pre)) (PreH2 : (count_pre <= 20)) (PreH3 : (1 <= number_width_pre)) (PreH4 : (number_width_pre <= 10)) (PreH5 : (2 <= (Z.shiftl (1) (count_pre)))) (PreH6 : ((Z.shiftl (1) (count_pre)) <= 1048576)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH10 : (FlatRows flat rows count_pre number_width_pre )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full best_first_pre (Z.shiftl (1) (count_pre)) )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (2 <= (Z.shiftl (1) (count_pre))) ” 
  &&  “ ((Z.shiftl (1) (count_pre)) <= 1048576) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ”
  &&  (((best_first_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg best_first_pre 1 (Z.shiftl (1) (count_pre)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_full result_pre (sum (lens)) )
.

Definition concatenating_numbers_dp_partial_solve_wit_2 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (bit_value: Z) (rest: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : (0 <= bit)) (PreH11 : (bit < count_pre)) (PreH12 : (1 <= bit_value)) (PreH13 : (bit_value < state_count)) (PreH14 : (0 <= rest)) (PreH15 : (rest < mask)) (PreH16 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH17 : (FlatRows flat rows count_pre number_width_pre )) (PreH18 : ((Zlength (choices)) = mask)) (PreH19 : (DPTablePrefix rows lens count_pre mask choices )) (PreH20 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (1 <= bit_value) ” 
  &&  “ (bit_value < state_count) ” 
  &&  “ (0 <= rest) ” 
  &&  “ (rest < mask) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = mask) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices ) ” 
  &&  “ (SelectedBitState mask count_pre bit bit_value rest ) ”
  &&  (((best_first_pre + (rest * sizeof(INT)))) # Int  |-> (Znth (rest - 0 ) choices 0))
  **  (IntArray.missing_i best_first_pre rest 0 mask choices )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
.

Definition concatenating_numbers_dp_partial_solve_wit_3_pure := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (previous_best >= 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : (0 <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices) (0)))) (PreH17 : (1 <= rest)) (PreH18 : (0 <= previous_best)) (PreH19 : (previous_best < count_pre)) (PreH20 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH21 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH22 : (FlatRows flat rows count_pre number_width_pre )) (PreH23 : (DPTablePrefix rows lens count_pre mask choices )) (PreH24 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "lengths" ) )) # Ptr  |-> lengths_pre)
  **  ((( &( "best_first" ) )) # Ptr  |-> best_first_pre)
  **  ((( &( "result" ) )) # Ptr  |-> result_pre)
  **  ((( &( "count" ) )) # Int  |-> count_pre)
  **  ((( &( "number_width" ) )) # Int  |-> number_width_pre)
  **  ((( &( "state_count" ) )) # Int  |-> state_count)
  **  ((( &( "mask" ) )) # Int  |-> mask)
  **  ((( &( "bit" ) )) # Int  |-> bit)
  **  ((( &( "rest" ) )) # Int  |-> rest)
  **  ((( &( "previous_best" ) )) # Int  |-> previous_best)
  **  ((( &( "bit_value" ) )) # Int  |-> bit_value)
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (0 <= previous_best) ” 
  &&  “ (previous_best < count_pre) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ”
.

Definition concatenating_numbers_dp_partial_solve_wit_3_aux := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (previous_best >= 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : (0 <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices) (0)))) (PreH17 : (1 <= rest)) (PreH18 : (0 <= previous_best)) (PreH19 : (previous_best < count_pre)) (PreH20 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH21 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH22 : (FlatRows flat rows count_pre number_width_pre )) (PreH23 : (DPTablePrefix rows lens count_pre mask choices )) (PreH24 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (0 <= previous_best) ” 
  &&  “ (previous_best < count_pre) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (previous_best >= 0) ” 
  &&  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (0 <= rest) ” 
  &&  “ (rest < mask) ” 
  &&  “ ((Zlength (choices)) = mask) ” 
  &&  “ (previous_best = (Znth (rest) (choices) (0))) ” 
  &&  “ (1 <= rest) ” 
  &&  “ (0 <= previous_best) ” 
  &&  “ (previous_best < count_pre) ” 
  &&  “ (BestIndexForMask rows lens count_pre rest previous_best ) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices ) ” 
  &&  “ (SelectedBitState mask count_pre bit bit_value rest ) ”
  &&  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
.

Definition concatenating_numbers_dp_partial_solve_wit_3 := concatenating_numbers_dp_partial_solve_wit_3_pure -> concatenating_numbers_dp_partial_solve_wit_3_aux.

Definition concatenating_numbers_dp_partial_solve_wit_4 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (PreH1 : (previous_best < 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (1 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (0 <= bit)) (PreH12 : (bit < count_pre)) (PreH13 : (0 <= rest)) (PreH14 : (rest < mask)) (PreH15 : ((Zlength (choices)) = mask)) (PreH16 : (previous_best = (Znth (rest) (choices) (0)))) (PreH17 : (rest = 0)) (PreH18 : (previous_best = (-1))) (PreH19 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH20 : (FlatRows flat rows count_pre number_width_pre )) (PreH21 : (DPTablePrefix rows lens count_pre mask choices )) (PreH22 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (previous_best < 0) ” 
  &&  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (0 <= rest) ” 
  &&  “ (rest < mask) ” 
  &&  “ ((Zlength (choices)) = mask) ” 
  &&  “ (previous_best = (Znth (rest) (choices) (0))) ” 
  &&  “ (rest = 0) ” 
  &&  “ (previous_best = (-1)) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices ) ” 
  &&  “ (SelectedBitState mask count_pre bit bit_value rest ) ”
  &&  (((best_first_pre + (mask * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_full result_pre (sum (lens)) )
.

Definition concatenating_numbers_dp_partial_solve_wit_5 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval > 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (retval > 0) ” 
  &&  “ (ConcatCompareSignOutcome rows lens bit previous_best retval ) ” 
  &&  “ (previous_best >= 0) ” 
  &&  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (0 <= rest) ” 
  &&  “ (rest < mask) ” 
  &&  “ ((Zlength (choices)) = mask) ” 
  &&  “ (previous_best = (Znth (rest) (choices) (0))) ” 
  &&  “ (1 <= rest) ” 
  &&  “ (0 <= previous_best) ” 
  &&  “ (previous_best < count_pre) ” 
  &&  “ (BestIndexForMask rows lens count_pre rest previous_best ) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices ) ” 
  &&  “ (SelectedBitState mask count_pre bit bit_value rest ) ”
  &&  (((best_first_pre + (mask * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_full result_pre (sum (lens)) )
.

Definition concatenating_numbers_dp_partial_solve_wit_6 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (state_count: Z) (mask: Z) (bit: Z) (rest: Z) (previous_best: Z) (bit_value: Z) (retval: Z) (PreH1 : (retval <= 0)) (PreH2 : (ConcatCompareSignOutcome rows lens bit previous_best retval )) (PreH3 : (previous_best >= 0)) (PreH4 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH5 : (1 <= count_pre)) (PreH6 : (count_pre <= 20)) (PreH7 : (1 <= number_width_pre)) (PreH8 : (number_width_pre <= 10)) (PreH9 : (1 <= (sum (lens)))) (PreH10 : ((sum (lens)) <= 200)) (PreH11 : (1 <= mask)) (PreH12 : (mask < state_count)) (PreH13 : (0 <= bit)) (PreH14 : (bit < count_pre)) (PreH15 : (0 <= rest)) (PreH16 : (rest < mask)) (PreH17 : ((Zlength (choices)) = mask)) (PreH18 : (previous_best = (Znth (rest) (choices) (0)))) (PreH19 : (1 <= rest)) (PreH20 : (0 <= previous_best)) (PreH21 : (previous_best < count_pre)) (PreH22 : (BestIndexForMask rows lens count_pre rest previous_best )) (PreH23 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH24 : (FlatRows flat rows count_pre number_width_pre )) (PreH25 : (DPTablePrefix rows lens count_pre mask choices )) (PreH26 : (SelectedBitState mask count_pre bit bit_value rest )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_seg best_first_pre mask state_count )
  **  (IntArray.undef_full result_pre (sum (lens)) )
|--
  “ (retval <= 0) ” 
  &&  “ (ConcatCompareSignOutcome rows lens bit previous_best retval ) ” 
  &&  “ (previous_best >= 0) ” 
  &&  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (0 <= bit) ” 
  &&  “ (bit < count_pre) ” 
  &&  “ (0 <= rest) ” 
  &&  “ (rest < mask) ” 
  &&  “ ((Zlength (choices)) = mask) ” 
  &&  “ (previous_best = (Znth (rest) (choices) (0))) ” 
  &&  “ (1 <= rest) ” 
  &&  “ (0 <= previous_best) ” 
  &&  “ (previous_best < count_pre) ” 
  &&  “ (BestIndexForMask rows lens count_pre rest previous_best ) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre mask choices ) ” 
  &&  “ (SelectedBitState mask count_pre bit bit_value rest ) ”
  &&  (((best_first_pre + (mask * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg best_first_pre (mask + 1 ) state_count )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg best_first_pre 0 mask choices )
  **  (IntArray.undef_full result_pre (sum (lens)) )
.

Definition concatenating_numbers_dp_partial_solve_wit_7 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (choices: (@list Z)) (output: (@list Z)) (result_length: Z) (mask: Z) (state_count: Z) (PreH1 : (mask <> 0)) (PreH2 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH3 : (1 <= count_pre)) (PreH4 : (count_pre <= 20)) (PreH5 : (1 <= number_width_pre)) (PreH6 : (number_width_pre <= 10)) (PreH7 : (1 <= (sum (lens)))) (PreH8 : ((sum (lens)) <= 200)) (PreH9 : (0 <= mask)) (PreH10 : (mask < state_count)) (PreH11 : (result_length = (Zlength (output)))) (PreH12 : (0 <= result_length)) (PreH13 : (result_length <= (sum (lens)))) (PreH14 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH15 : (FlatRows flat rows count_pre number_width_pre )) (PreH16 : ((Zlength (choices)) = state_count)) (PreH17 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH18 : (GreedyOutputPrefix rows lens count_pre mask output )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (mask <> 0) ” 
  &&  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (0 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ (result_length <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask output ) ”
  &&  (((best_first_pre + (mask * sizeof(INT)))) # Int  |-> (Znth mask choices 0))
  **  (IntArray.missing_i best_first_pre mask 0 state_count choices )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
.

Definition concatenating_numbers_dp_partial_solve_wit_8 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH2 : (1 <= count_pre)) (PreH3 : (count_pre <= 20)) (PreH4 : (1 <= number_width_pre)) (PreH5 : (number_width_pre <= 10)) (PreH6 : (1 <= (sum (lens)))) (PreH7 : ((sum (lens)) <= 200)) (PreH8 : (1 <= mask)) (PreH9 : (mask < state_count)) (PreH10 : ((Zlength (choices)) = state_count)) (PreH11 : (first = (Znth (mask) (choices) (0)))) (PreH12 : (0 <= first)) (PreH13 : (first < count_pre)) (PreH14 : (0 <= position)) (PreH15 : (position <= (Znth (first) (lens) (0)))) (PreH16 : (1 <= (Znth (first) (lens) (0)))) (PreH17 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH18 : (result_length = (Zlength (output)))) (PreH19 : (0 <= result_length)) (PreH20 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH21 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH22 : (FlatRows flat rows count_pre number_width_pre )) (PreH23 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH24 : (BestIndexForMask rows lens count_pre mask first )) (PreH25 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH26 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (first = (Znth (mask) (choices) (0))) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < count_pre) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= (Znth (first) (lens) (0))) ” 
  &&  “ (1 <= (Znth (first) (lens) (0))) ” 
  &&  “ ((Znth (first) (lens) (0)) <= number_width_pre) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (BestIndexForMask rows lens count_pre mask first ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask prior ) ” 
  &&  “ (AppendRowPrefix rows lens prior first position output ) ”
  &&  (((lengths_pre + (first * sizeof(INT)))) # Int  |-> (Znth first lens 0))
  **  (IntArray.missing_i lengths_pre first 0 count_pre lens )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
.

Definition concatenating_numbers_dp_partial_solve_wit_9 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (0 <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (position <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (first <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (position >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (0 <= ((first * number_width_pre ) + position ))) (PreH12 : (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (mask <= INT_MAX)) (PreH15 : (state_count <= INT_MAX)) (PreH16 : (result_length >= INT_MIN)) (PreH17 : (mask >= INT_MIN)) (PreH18 : (state_count >= INT_MIN)) (PreH19 : (position < (Znth first lens 0))) (PreH20 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (1 <= mask)) (PreH28 : (mask < state_count)) (PreH29 : ((Zlength (choices)) = state_count)) (PreH30 : (first = (Znth (mask) (choices) (0)))) (PreH31 : (0 <= first)) (PreH32 : (first < count_pre)) (PreH33 : (0 <= position)) (PreH34 : (position <= (Znth (first) (lens) (0)))) (PreH35 : (1 <= (Znth (first) (lens) (0)))) (PreH36 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH37 : (result_length = (Zlength (output)))) (PreH38 : (0 <= result_length)) (PreH39 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH40 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH41 : (FlatRows flat rows count_pre number_width_pre )) (PreH42 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH43 : (BestIndexForMask rows lens count_pre mask first )) (PreH44 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH45 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (0 <= result_length) ” 
  &&  “ (result_length < (sum (lens))) ” 
  &&  “ (count_pre <= INT_MAX) ” 
  &&  “ (position <= INT_MAX) ” 
  &&  “ (number_width_pre <= INT_MAX) ” 
  &&  “ (first <= INT_MAX) ” 
  &&  “ (count_pre >= INT_MIN) ” 
  &&  “ (position >= INT_MIN) ” 
  &&  “ (number_width_pre >= INT_MIN) ” 
  &&  “ (first >= INT_MIN) ” 
  &&  “ (0 <= ((first * number_width_pre ) + position )) ” 
  &&  “ (((first * number_width_pre ) + position ) < (count_pre * number_width_pre )) ” 
  &&  “ (result_length <= INT_MAX) ” 
  &&  “ (mask <= INT_MAX) ” 
  &&  “ (state_count <= INT_MAX) ” 
  &&  “ (result_length >= INT_MIN) ” 
  &&  “ (mask >= INT_MIN) ” 
  &&  “ (state_count >= INT_MIN) ” 
  &&  “ (position < (Znth first lens 0)) ” 
  &&  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (first = (Znth (mask) (choices) (0))) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < count_pre) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= (Znth (first) (lens) (0))) ” 
  &&  “ (1 <= (Znth (first) (lens) (0))) ” 
  &&  “ ((Znth (first) (lens) (0)) <= number_width_pre) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (BestIndexForMask rows lens count_pre mask first ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask prior ) ” 
  &&  “ (AppendRowPrefix rows lens prior first position output ) ”
  &&  (((numbers_pre + (((first * number_width_pre ) + position ) * sizeof(INT)))) # Int  |-> (Znth ((first * number_width_pre ) + position ) flat 0))
  **  (IntArray.missing_i numbers_pre ((first * number_width_pre ) + position ) 0 (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
.

Definition concatenating_numbers_dp_partial_solve_wit_10 := 
forall (result_pre: Z) (best_first_pre: Z) (lengths_pre: Z) (number_width_pre: Z) (count_pre: Z) (numbers_pre: Z) (flat: (@list Z)) (lens: (@list Z)) (rows: (@list (@list Z))) (prior: (@list Z)) (output: (@list Z)) (result_length: Z) (position: Z) (first: Z) (choices: (@list Z)) (mask: Z) (state_count: Z) (PreH1 : (0 <= result_length)) (PreH2 : (result_length < (sum (lens)))) (PreH3 : (count_pre <= INT_MAX)) (PreH4 : (position <= INT_MAX)) (PreH5 : (number_width_pre <= INT_MAX)) (PreH6 : (first <= INT_MAX)) (PreH7 : (count_pre >= INT_MIN)) (PreH8 : (position >= INT_MIN)) (PreH9 : (number_width_pre >= INT_MIN)) (PreH10 : (first >= INT_MIN)) (PreH11 : (0 <= ((first * number_width_pre ) + position ))) (PreH12 : (((first * number_width_pre ) + position ) < (count_pre * number_width_pre ))) (PreH13 : (result_length <= INT_MAX)) (PreH14 : (mask <= INT_MAX)) (PreH15 : (state_count <= INT_MAX)) (PreH16 : (result_length >= INT_MIN)) (PreH17 : (mask >= INT_MIN)) (PreH18 : (state_count >= INT_MIN)) (PreH19 : (position < (Znth first lens 0))) (PreH20 : (state_count = (Z.shiftl (1) (count_pre)))) (PreH21 : (1 <= count_pre)) (PreH22 : (count_pre <= 20)) (PreH23 : (1 <= number_width_pre)) (PreH24 : (number_width_pre <= 10)) (PreH25 : (1 <= (sum (lens)))) (PreH26 : ((sum (lens)) <= 200)) (PreH27 : (1 <= mask)) (PreH28 : (mask < state_count)) (PreH29 : ((Zlength (choices)) = state_count)) (PreH30 : (first = (Znth (mask) (choices) (0)))) (PreH31 : (0 <= first)) (PreH32 : (first < count_pre)) (PreH33 : (0 <= position)) (PreH34 : (position <= (Znth (first) (lens) (0)))) (PreH35 : (1 <= (Znth (first) (lens) (0)))) (PreH36 : ((Znth (first) (lens) (0)) <= number_width_pre)) (PreH37 : (result_length = (Zlength (output)))) (PreH38 : (0 <= result_length)) (PreH39 : ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens)))) (PreH40 : (RowsWellFormed rows lens count_pre number_width_pre )) (PreH41 : (FlatRows flat rows count_pre number_width_pre )) (PreH42 : (DPTablePrefix rows lens count_pre state_count choices )) (PreH43 : (BestIndexForMask rows lens count_pre mask first )) (PreH44 : (GreedyOutputPrefix rows lens count_pre mask prior )) (PreH45 : (AppendRowPrefix rows lens prior first position output )) ,
  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
  **  (IntArray.undef_seg result_pre result_length (sum (lens)) )
|--
  “ (0 <= result_length) ” 
  &&  “ (result_length < (sum (lens))) ” 
  &&  “ (count_pre <= INT_MAX) ” 
  &&  “ (position <= INT_MAX) ” 
  &&  “ (number_width_pre <= INT_MAX) ” 
  &&  “ (first <= INT_MAX) ” 
  &&  “ (count_pre >= INT_MIN) ” 
  &&  “ (position >= INT_MIN) ” 
  &&  “ (number_width_pre >= INT_MIN) ” 
  &&  “ (first >= INT_MIN) ” 
  &&  “ (0 <= ((first * number_width_pre ) + position )) ” 
  &&  “ (((first * number_width_pre ) + position ) < (count_pre * number_width_pre )) ” 
  &&  “ (result_length <= INT_MAX) ” 
  &&  “ (mask <= INT_MAX) ” 
  &&  “ (state_count <= INT_MAX) ” 
  &&  “ (result_length >= INT_MIN) ” 
  &&  “ (mask >= INT_MIN) ” 
  &&  “ (state_count >= INT_MIN) ” 
  &&  “ (position < (Znth first lens 0)) ” 
  &&  “ (state_count = (Z.shiftl (1) (count_pre))) ” 
  &&  “ (1 <= count_pre) ” 
  &&  “ (count_pre <= 20) ” 
  &&  “ (1 <= number_width_pre) ” 
  &&  “ (number_width_pre <= 10) ” 
  &&  “ (1 <= (sum (lens))) ” 
  &&  “ ((sum (lens)) <= 200) ” 
  &&  “ (1 <= mask) ” 
  &&  “ (mask < state_count) ” 
  &&  “ ((Zlength (choices)) = state_count) ” 
  &&  “ (first = (Znth (mask) (choices) (0))) ” 
  &&  “ (0 <= first) ” 
  &&  “ (first < count_pre) ” 
  &&  “ (0 <= position) ” 
  &&  “ (position <= (Znth (first) (lens) (0))) ” 
  &&  “ (1 <= (Znth (first) (lens) (0))) ” 
  &&  “ ((Znth (first) (lens) (0)) <= number_width_pre) ” 
  &&  “ (result_length = (Zlength (output))) ” 
  &&  “ (0 <= result_length) ” 
  &&  “ ((result_length + ((Znth (first) (lens) (0)) - position ) ) <= (sum (lens))) ” 
  &&  “ (RowsWellFormed rows lens count_pre number_width_pre ) ” 
  &&  “ (FlatRows flat rows count_pre number_width_pre ) ” 
  &&  “ (DPTablePrefix rows lens count_pre state_count choices ) ” 
  &&  “ (BestIndexForMask rows lens count_pre mask first ) ” 
  &&  “ (GreedyOutputPrefix rows lens count_pre mask prior ) ” 
  &&  “ (AppendRowPrefix rows lens prior first position output ) ”
  &&  (((result_pre + (result_length * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg result_pre (result_length + 1 ) (sum (lens)) )
  **  (IntArray.full numbers_pre (count_pre * number_width_pre ) flat )
  **  (IntArray.full lengths_pre count_pre lens )
  **  (IntArray.full best_first_pre state_count choices )
  **  (IntArray.seg result_pre 0 result_length output )
.

Module Type VC_Correct.


Axiom proof_of_compare_concatenated_order_safety_wit_1 : compare_concatenated_order_safety_wit_1.
Axiom proof_of_compare_concatenated_order_safety_wit_2 : compare_concatenated_order_safety_wit_2.
Axiom proof_of_compare_concatenated_order_safety_wit_3 : compare_concatenated_order_safety_wit_3.
Axiom proof_of_compare_concatenated_order_safety_wit_4 : compare_concatenated_order_safety_wit_4.
Axiom proof_of_compare_concatenated_order_safety_wit_5 : compare_concatenated_order_safety_wit_5.
Axiom proof_of_compare_concatenated_order_safety_wit_6 : compare_concatenated_order_safety_wit_6.
Axiom proof_of_compare_concatenated_order_safety_wit_7 : compare_concatenated_order_safety_wit_7.
Axiom proof_of_compare_concatenated_order_safety_wit_8 : compare_concatenated_order_safety_wit_8.
Axiom proof_of_compare_concatenated_order_safety_wit_9 : compare_concatenated_order_safety_wit_9.
Axiom proof_of_compare_concatenated_order_safety_wit_10 : compare_concatenated_order_safety_wit_10.
Axiom proof_of_compare_concatenated_order_safety_wit_11 : compare_concatenated_order_safety_wit_11.
Axiom proof_of_compare_concatenated_order_safety_wit_12 : compare_concatenated_order_safety_wit_12.
Axiom proof_of_compare_concatenated_order_safety_wit_13 : compare_concatenated_order_safety_wit_13.
Axiom proof_of_compare_concatenated_order_safety_wit_14 : compare_concatenated_order_safety_wit_14.
Axiom proof_of_compare_concatenated_order_safety_wit_15 : compare_concatenated_order_safety_wit_15.
Axiom proof_of_compare_concatenated_order_safety_wit_16 : compare_concatenated_order_safety_wit_16.
Axiom proof_of_compare_concatenated_order_safety_wit_17 : compare_concatenated_order_safety_wit_17.
Axiom proof_of_compare_concatenated_order_entail_wit_1 : compare_concatenated_order_entail_wit_1.
Axiom proof_of_compare_concatenated_order_entail_wit_2 : compare_concatenated_order_entail_wit_2.
Axiom proof_of_compare_concatenated_order_entail_wit_3 : compare_concatenated_order_entail_wit_3.
Axiom proof_of_compare_concatenated_order_entail_wit_4 : compare_concatenated_order_entail_wit_4.
Axiom proof_of_compare_concatenated_order_entail_wit_5 : compare_concatenated_order_entail_wit_5.
Axiom proof_of_compare_concatenated_order_entail_wit_6_1 : compare_concatenated_order_entail_wit_6_1.
Axiom proof_of_compare_concatenated_order_entail_wit_6_2 : compare_concatenated_order_entail_wit_6_2.
Axiom proof_of_compare_concatenated_order_entail_wit_7 : compare_concatenated_order_entail_wit_7.
Axiom proof_of_compare_concatenated_order_entail_wit_8 : compare_concatenated_order_entail_wit_8.
Axiom proof_of_compare_concatenated_order_entail_wit_9 : compare_concatenated_order_entail_wit_9.
Axiom proof_of_compare_concatenated_order_entail_wit_10 : compare_concatenated_order_entail_wit_10.
Axiom proof_of_compare_concatenated_order_entail_wit_11_1 : compare_concatenated_order_entail_wit_11_1.
Axiom proof_of_compare_concatenated_order_entail_wit_11_2 : compare_concatenated_order_entail_wit_11_2.
Axiom proof_of_compare_concatenated_order_entail_wit_12 : compare_concatenated_order_entail_wit_12.
Axiom proof_of_compare_concatenated_order_return_wit_1 : compare_concatenated_order_return_wit_1.
Axiom proof_of_compare_concatenated_order_return_wit_2 : compare_concatenated_order_return_wit_2.
Axiom proof_of_compare_concatenated_order_return_wit_3 : compare_concatenated_order_return_wit_3.
Axiom proof_of_compare_concatenated_order_partial_solve_wit_1 : compare_concatenated_order_partial_solve_wit_1.
Axiom proof_of_compare_concatenated_order_partial_solve_wit_2 : compare_concatenated_order_partial_solve_wit_2.
Axiom proof_of_compare_concatenated_order_partial_solve_wit_3 : compare_concatenated_order_partial_solve_wit_3.
Axiom proof_of_compare_concatenated_order_partial_solve_wit_4 : compare_concatenated_order_partial_solve_wit_4.
Axiom proof_of_compare_concatenated_order_partial_solve_wit_5 : compare_concatenated_order_partial_solve_wit_5.
Axiom proof_of_compare_concatenated_order_partial_solve_wit_6 : compare_concatenated_order_partial_solve_wit_6.
Axiom proof_of_concatenating_numbers_dp_safety_wit_1 : concatenating_numbers_dp_safety_wit_1.
Axiom proof_of_concatenating_numbers_dp_safety_wit_2 : concatenating_numbers_dp_safety_wit_2.
Axiom proof_of_concatenating_numbers_dp_safety_wit_3 : concatenating_numbers_dp_safety_wit_3.
Axiom proof_of_concatenating_numbers_dp_safety_wit_4 : concatenating_numbers_dp_safety_wit_4.
Axiom proof_of_concatenating_numbers_dp_safety_wit_5 : concatenating_numbers_dp_safety_wit_5.
Axiom proof_of_concatenating_numbers_dp_safety_wit_6 : concatenating_numbers_dp_safety_wit_6.
Axiom proof_of_concatenating_numbers_dp_safety_wit_7 : concatenating_numbers_dp_safety_wit_7.
Axiom proof_of_concatenating_numbers_dp_safety_wit_8 : concatenating_numbers_dp_safety_wit_8.
Axiom proof_of_concatenating_numbers_dp_safety_wit_9 : concatenating_numbers_dp_safety_wit_9.
Axiom proof_of_concatenating_numbers_dp_safety_wit_10 : concatenating_numbers_dp_safety_wit_10.
Axiom proof_of_concatenating_numbers_dp_safety_wit_11 : concatenating_numbers_dp_safety_wit_11.
Axiom proof_of_concatenating_numbers_dp_safety_wit_12 : concatenating_numbers_dp_safety_wit_12.
Axiom proof_of_concatenating_numbers_dp_safety_wit_13 : concatenating_numbers_dp_safety_wit_13.
Axiom proof_of_concatenating_numbers_dp_safety_wit_14 : concatenating_numbers_dp_safety_wit_14.
Axiom proof_of_concatenating_numbers_dp_safety_wit_15 : concatenating_numbers_dp_safety_wit_15.
Axiom proof_of_concatenating_numbers_dp_safety_wit_16 : concatenating_numbers_dp_safety_wit_16.
Axiom proof_of_concatenating_numbers_dp_safety_wit_17 : concatenating_numbers_dp_safety_wit_17.
Axiom proof_of_concatenating_numbers_dp_safety_wit_18 : concatenating_numbers_dp_safety_wit_18.
Axiom proof_of_concatenating_numbers_dp_safety_wit_19 : concatenating_numbers_dp_safety_wit_19.
Axiom proof_of_concatenating_numbers_dp_safety_wit_20 : concatenating_numbers_dp_safety_wit_20.
Axiom proof_of_concatenating_numbers_dp_safety_wit_21 : concatenating_numbers_dp_safety_wit_21.
Axiom proof_of_concatenating_numbers_dp_safety_wit_22 : concatenating_numbers_dp_safety_wit_22.
Axiom proof_of_concatenating_numbers_dp_safety_wit_23 : concatenating_numbers_dp_safety_wit_23.
Axiom proof_of_concatenating_numbers_dp_safety_wit_24 : concatenating_numbers_dp_safety_wit_24.
Axiom proof_of_concatenating_numbers_dp_safety_wit_25 : concatenating_numbers_dp_safety_wit_25.
Axiom proof_of_concatenating_numbers_dp_safety_wit_26 : concatenating_numbers_dp_safety_wit_26.
Axiom proof_of_concatenating_numbers_dp_safety_wit_27 : concatenating_numbers_dp_safety_wit_27.
Axiom proof_of_concatenating_numbers_dp_safety_wit_28 : concatenating_numbers_dp_safety_wit_28.
Axiom proof_of_concatenating_numbers_dp_safety_wit_29 : concatenating_numbers_dp_safety_wit_29.
Axiom proof_of_concatenating_numbers_dp_entail_wit_1 : concatenating_numbers_dp_entail_wit_1.
Axiom proof_of_concatenating_numbers_dp_entail_wit_2 : concatenating_numbers_dp_entail_wit_2.
Axiom proof_of_concatenating_numbers_dp_entail_wit_3 : concatenating_numbers_dp_entail_wit_3.
Axiom proof_of_concatenating_numbers_dp_entail_wit_4 : concatenating_numbers_dp_entail_wit_4.
Axiom proof_of_concatenating_numbers_dp_entail_wit_5 : concatenating_numbers_dp_entail_wit_5.
Axiom proof_of_concatenating_numbers_dp_entail_wit_6_1 : concatenating_numbers_dp_entail_wit_6_1.
Axiom proof_of_concatenating_numbers_dp_entail_wit_6_2 : concatenating_numbers_dp_entail_wit_6_2.
Axiom proof_of_concatenating_numbers_dp_entail_wit_6_3 : concatenating_numbers_dp_entail_wit_6_3.
Axiom proof_of_concatenating_numbers_dp_entail_wit_7 : concatenating_numbers_dp_entail_wit_7.
Axiom proof_of_concatenating_numbers_dp_entail_wit_8 : concatenating_numbers_dp_entail_wit_8.
Axiom proof_of_concatenating_numbers_dp_entail_wit_9 : concatenating_numbers_dp_entail_wit_9.
Axiom proof_of_concatenating_numbers_dp_entail_wit_10 : concatenating_numbers_dp_entail_wit_10.
Axiom proof_of_concatenating_numbers_dp_entail_wit_11 : concatenating_numbers_dp_entail_wit_11.
Axiom proof_of_concatenating_numbers_dp_entail_wit_12 : concatenating_numbers_dp_entail_wit_12.
Axiom proof_of_concatenating_numbers_dp_entail_wit_13 : concatenating_numbers_dp_entail_wit_13.
Axiom proof_of_concatenating_numbers_dp_entail_wit_14 : concatenating_numbers_dp_entail_wit_14.
Axiom proof_of_concatenating_numbers_dp_return_wit_1 : concatenating_numbers_dp_return_wit_1.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_1 : concatenating_numbers_dp_partial_solve_wit_1.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_2 : concatenating_numbers_dp_partial_solve_wit_2.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_3_pure : concatenating_numbers_dp_partial_solve_wit_3_pure.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_3 : concatenating_numbers_dp_partial_solve_wit_3.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_4 : concatenating_numbers_dp_partial_solve_wit_4.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_5 : concatenating_numbers_dp_partial_solve_wit_5.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_6 : concatenating_numbers_dp_partial_solve_wit_6.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_7 : concatenating_numbers_dp_partial_solve_wit_7.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_8 : concatenating_numbers_dp_partial_solve_wit_8.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_9 : concatenating_numbers_dp_partial_solve_wit_9.
Axiom proof_of_concatenating_numbers_dp_partial_solve_wit_10 : concatenating_numbers_dp_partial_solve_wit_10.

End VC_Correct.
