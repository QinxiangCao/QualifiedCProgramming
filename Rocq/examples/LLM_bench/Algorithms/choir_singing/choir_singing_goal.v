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
Require Import SimpleC.EE.LLM_bench.Algorithms.choir_singing.choir_singing_lib.
Local Open Scope sac.

(*----- Function choir_singing -----*)

Definition choir_singing_safety_wit_1 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.undef_full dp_left_pre numsSize_pre )
  **  (IntArray.undef_full dp_right_pre numsSize_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition choir_singing_safety_wit_2 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_written: (@list Z)) (left_written: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written i )) (PreH8 : (ChoirOnesPrefix right_written i )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.seg dp_left_pre 0 i left_written )
  **  (IntArray.undef_seg dp_left_pre i numsSize_pre )
  **  (IntArray.seg dp_right_pre 0 i right_written )
  **  (IntArray.undef_seg dp_right_pre i numsSize_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_3 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_written: (@list Z)) (left_written: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written i )) (PreH8 : (ChoirOnesPrefix right_written i )) ,
  (IntArray.seg dp_left_pre 0 (i + 1 ) (app (left_written) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_left_pre (i + 1 ) numsSize_pre )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.seg dp_right_pre 0 i right_written )
  **  (IntArray.undef_seg dp_right_pre i numsSize_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_4 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_written: (@list Z)) (left_written: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written i )) (PreH8 : (ChoirOnesPrefix right_written i )) ,
  (IntArray.seg dp_right_pre 0 (i + 1 ) (app (right_written) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_right_pre (i + 1 ) numsSize_pre )
  **  (IntArray.seg dp_left_pre 0 (i + 1 ) (app (left_written) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_left_pre (i + 1 ) numsSize_pre )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition choir_singing_safety_wit_5 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values: (@list Z)) (right_values: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirOnesFull left_values numsSize_pre )) (PreH5 : (ChoirOnesFull right_values numsSize_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition choir_singing_safety_wit_6 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values i )) (PreH8 : (ChoirOnesFull right_values numsSize_pre )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition choir_singing_safety_wit_7 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values i )) (PreH8 : (ChoirOnesFull right_values numsSize_pre )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_8 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : ((-1) <= j)) (PreH7 : (j < i)) (PreH8 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH9 : (ChoirOnesFull right_values numsSize_pre )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition choir_singing_safety_wit_9 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (((Znth j left_values 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j left_values 0) + 1 )) ”
) \/
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (((Znth j left_values 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j left_values 0) + 1 )) ”
).

Definition choir_singing_safety_wit_9_split_goal_1 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (((Znth j left_values 0) + 1 ) <= INT_MAX) ”
.

Definition choir_singing_safety_wit_9_split_goal_2 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((INT_MIN) <= ((Znth j left_values 0) + 1 )) ”
.

Definition choir_singing_safety_wit_10 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_11 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values 0) + 1 ) > (Znth i left_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (((Znth j left_values 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j left_values 0) + 1 )) ”
) \/
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values 0) + 1 ) > (Znth i left_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (((Znth j left_values 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j left_values 0) + 1 )) ”
).

Definition choir_singing_safety_wit_11_split_goal_1 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values 0) + 1 ) > (Znth i left_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (((Znth j left_values 0) + 1 ) <= INT_MAX) ”
.

Definition choir_singing_safety_wit_11_split_goal_2 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values 0) + 1 ) > (Znth i left_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((INT_MIN) <= ((Znth j left_values 0) + 1 )) ”
.

Definition choir_singing_safety_wit_12 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values 0) + 1 ) > (Znth i left_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_13 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values 0) + 1 ) > (Znth i left_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre (replace_Znth (i) (((Znth j left_values 0) + 1 )) (left_values)) )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition choir_singing_safety_wit_14 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) >= (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition choir_singing_safety_wit_15 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values 0) + 1 ) <= (Znth i left_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition choir_singing_safety_wit_16 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values: (@list Z)) (right_values: (@list Z)) (i: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values (i + 1 ) )) (PreH7 : (ChoirOnesFull right_values numsSize_pre )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition choir_singing_safety_wit_17 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values: (@list Z)) (right_values: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH5 : (ChoirOnesFull right_values numsSize_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((numsSize_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numsSize_pre - 1 )) ”
.

Definition choir_singing_safety_wit_18 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values: (@list Z)) (right_values: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH5 : (ChoirOnesFull right_values numsSize_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_19 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (i: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (0 <= (i + 1 ))) (PreH5 : ((i + 1 ) <= numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH7 : (ChoirDPRightSuffix heights right_values (i + 1 ) )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition choir_singing_safety_wit_20 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= (i + 1 ))) (PreH6 : ((i + 1 ) <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH8 : (ChoirDPRightSuffix heights right_values (i + 1 ) )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition choir_singing_safety_wit_21 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= (i + 1 ))) (PreH6 : ((i + 1 ) <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH8 : (ChoirDPRightSuffix heights right_values (i + 1 ) )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_22 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (((Znth j right_values 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j right_values 0) + 1 )) ”
) \/
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (((Znth j right_values 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j right_values 0) + 1 )) ”
).

Definition choir_singing_safety_wit_22_split_goal_1 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (((Znth j right_values 0) + 1 ) <= INT_MAX) ”
.

Definition choir_singing_safety_wit_22_split_goal_2 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ ((INT_MIN) <= ((Znth j right_values 0) + 1 )) ”
.

Definition choir_singing_safety_wit_23 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_24 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values 0) + 1 ) > (Znth i right_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (((Znth j right_values 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j right_values 0) + 1 )) ”
) \/
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values 0) + 1 ) > (Znth i right_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (((Znth j right_values 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j right_values 0) + 1 )) ”
).

Definition choir_singing_safety_wit_24_split_goal_1 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values 0) + 1 ) > (Znth i right_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (((Znth j right_values 0) + 1 ) <= INT_MAX) ”
.

Definition choir_singing_safety_wit_24_split_goal_2 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values 0) + 1 ) > (Znth i right_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ ((INT_MIN) <= ((Znth j right_values 0) + 1 )) ”
.

Definition choir_singing_safety_wit_25 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values 0) + 1 ) > (Znth i right_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_26 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values 0) + 1 ) > (Znth i right_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre (replace_Znth (i) (((Znth j right_values 0) + 1 )) (right_values)) )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition choir_singing_safety_wit_27 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) >= (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition choir_singing_safety_wit_28 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values 0) + 1 ) <= (Znth i right_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition choir_singing_safety_wit_29 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values: (@list Z)) (right_values: (@list Z)) (i: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH7 : (ChoirDPRightSuffix heights right_values i )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition choir_singing_safety_wit_30 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values: (@list Z)) (right_values: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH5 : (ChoirDPRightSuffix heights right_values 0 )) ,
  ((( &( "max_choir" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition choir_singing_safety_wit_31 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values: (@list Z)) (right_values: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH5 : (ChoirDPRightSuffix heights right_values 0 )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "max_choir" ) )) # Int  |-> 0)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition choir_singing_safety_wit_32 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ (((Znth k left_values 0) + (Znth k right_values 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth k left_values 0) + (Znth k right_values 0) )) ”
) \/
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ (((Znth k left_values 0) + (Znth k right_values 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth k left_values 0) + (Znth k right_values 0) )) ”
).

Definition choir_singing_safety_wit_32_split_goal_1 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ (((Znth k left_values 0) + (Znth k right_values 0) ) <= INT_MAX) ”
.

Definition choir_singing_safety_wit_32_split_goal_2 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ ((INT_MIN) <= ((Znth k left_values 0) + (Znth k right_values 0) )) ”
.

Definition choir_singing_safety_wit_33 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ ((((Znth k left_values 0) + (Znth k right_values 0) ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth k left_values 0) + (Znth k right_values 0) ) - 1 )) ”
) \/
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ ((((Znth k left_values 0) + (Znth k right_values 0) ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth k left_values 0) + (Znth k right_values 0) ) - 1 )) ”
).

Definition choir_singing_safety_wit_33_split_goal_1 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ ((((Znth k left_values 0) + (Znth k right_values 0) ) - 1 ) <= INT_MAX) ”
.

Definition choir_singing_safety_wit_33_split_goal_2 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ ((INT_MIN) <= (((Znth k left_values 0) + (Znth k right_values 0) ) - 1 )) ”
.

Definition choir_singing_safety_wit_34 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ (((Znth k left_values 0) + (Znth k right_values 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth k left_values 0) + (Znth k right_values 0) )) ”
) \/
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ (((Znth k left_values 0) + (Znth k right_values 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth k left_values 0) + (Znth k right_values 0) )) ”
).

Definition choir_singing_safety_wit_34_split_goal_1 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ (((Znth k left_values 0) + (Znth k right_values 0) ) <= INT_MAX) ”
.

Definition choir_singing_safety_wit_34_split_goal_2 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ ((INT_MIN) <= ((Znth k left_values 0) + (Znth k right_values 0) )) ”
.

Definition choir_singing_safety_wit_35 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition choir_singing_safety_wit_36 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> (((Znth k left_values 0) + (Znth k right_values 0) ) - 1 ))
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition choir_singing_safety_wit_37 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) <= max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition choir_singing_safety_wit_38 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values: (@list Z)) (right_values: (@list Z)) (max_choir: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (1 <= max_choir)) (PreH5 : (max_choir <= numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH7 : (ChoirDPRightSuffix heights right_values 0 )) (PreH8 : (ChoirBestPrefix heights numsSize_pre max_choir )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp_left" ) )) # Ptr  |-> dp_left_pre)
  **  ((( &( "dp_right" ) )) # Ptr  |-> dp_right_pre)
  **  ((( &( "max_choir" ) )) # Int  |-> max_choir)
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((numsSize_pre - max_choir ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numsSize_pre - max_choir )) ”
.

Definition choir_singing_entail_wit_1 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.undef_full dp_left_pre numsSize_pre )
  **  (IntArray.undef_full dp_right_pre numsSize_pre )
|--
  EX (right_written: (@list Z))  (left_written: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (ChoirOnesPrefix left_written 0 ) ” 
  &&  “ (ChoirOnesPrefix right_written 0 ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.seg dp_left_pre 0 0 left_written )
  **  (IntArray.undef_seg dp_left_pre 0 numsSize_pre )
  **  (IntArray.seg dp_right_pre 0 0 right_written )
  **  (IntArray.undef_seg dp_right_pre 0 numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) ,
  TT && emp 
|--
  “ (ChoirOnesPrefix (@nil Z) 0 ) ” 
  &&  “ (ChoirOnesPrefix (@nil Z) 0 ) ”
  &&  emp
).

Definition choir_singing_entail_wit_1_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) ,
  (ChoirOnesPrefix (@nil Z) 0 )
.

Definition choir_singing_entail_wit_1_split_goal_2 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) ,
  (ChoirOnesPrefix (@nil Z) 0 )
.

Definition choir_singing_entail_wit_2 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_written_2: (@list Z)) (left_written_2: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written_2 i )) (PreH8 : (ChoirOnesPrefix right_written_2 i )) ,
  (IntArray.seg dp_right_pre 0 (i + 1 ) (app (right_written_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_right_pre (i + 1 ) numsSize_pre )
  **  (IntArray.seg dp_left_pre 0 (i + 1 ) (app (left_written_2) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_left_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  EX (right_written: (@list Z))  (left_written: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (ChoirOnesPrefix left_written (i + 1 ) ) ” 
  &&  “ (ChoirOnesPrefix right_written (i + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.seg dp_left_pre 0 (i + 1 ) left_written )
  **  (IntArray.undef_seg dp_left_pre (i + 1 ) numsSize_pre )
  **  (IntArray.seg dp_right_pre 0 (i + 1 ) right_written )
  **  (IntArray.undef_seg dp_right_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_written_2: (@list Z)) (left_written_2: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written_2 i )) (PreH8 : (ChoirOnesPrefix right_written_2 i )) ,
  TT && emp 
|--
  “ (ChoirOnesPrefix (app (right_written_2) ((cons (1) ((@nil Z))))) (i + 1 ) ) ” 
  &&  “ (ChoirOnesPrefix (app (left_written_2) ((cons (1) ((@nil Z))))) (i + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_2_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_written_2: (@list Z)) (left_written_2: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written_2 i )) (PreH8 : (ChoirOnesPrefix right_written_2 i )) ,
  (ChoirOnesPrefix (app (right_written_2) ((cons (1) ((@nil Z))))) (i + 1 ) )
.

Definition choir_singing_entail_wit_2_split_goal_2 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_written_2: (@list Z)) (left_written_2: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written_2 i )) (PreH8 : (ChoirOnesPrefix right_written_2 i )) ,
  (ChoirOnesPrefix (app (left_written_2) ((cons (1) ((@nil Z))))) (i + 1 ) )
.

Definition choir_singing_entail_wit_3 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_written: (@list Z)) (left_written: (@list Z)) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written i )) (PreH8 : (ChoirOnesPrefix right_written i )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.seg dp_left_pre 0 i left_written )
  **  (IntArray.undef_seg dp_left_pre i numsSize_pre )
  **  (IntArray.seg dp_right_pre 0 i right_written )
  **  (IntArray.undef_seg dp_right_pre i numsSize_pre )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (ChoirOnesFull left_values numsSize_pre ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (heights: (@list Z)) (right_written: (@list Z)) (left_written: (@list Z)) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written i )) (PreH8 : (ChoirOnesPrefix right_written i )) ,
  (IntArray.seg dp_left_pre 0 i left_written )
  **  (IntArray.seg dp_right_pre 0 i right_written )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (ChoirOnesFull left_values numsSize_pre ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
).

Definition choir_singing_entail_wit_4 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirOnesFull left_values_2 numsSize_pre )) (PreH5 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values 0 ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirOnesFull left_values_2 numsSize_pre )) (PreH5 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  TT && emp 
|--
  “ (ChoirDPLeftPrefix heights left_values_2 0 ) ”
  &&  emp
).

Definition choir_singing_entail_wit_4_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirOnesFull left_values_2 numsSize_pre )) (PreH5 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (ChoirDPLeftPrefix heights left_values_2 0 )
.

Definition choir_singing_entail_wit_5 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 i )) (PreH8 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i ((i - 1 ) + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 i )) (PreH8 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  TT && emp 
|--
  “ (ChoirLeftInnerProgress heights left_values_2 i ((i - 1 ) + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_5_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 i )) (PreH8 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (ChoirLeftInnerProgress heights left_values_2 i ((i - 1 ) + 1 ) )
.

Definition choir_singing_entail_wit_6_1 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values_2 0) + 1 ) > (Znth i left_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre (replace_Znth (i) (((Znth j left_values_2 0) + 1 )) (left_values_2)) )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i ((j - 1 ) + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values_2 0) + 1 ) > (Znth i left_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  TT && emp 
|--
  “ (ChoirLeftInnerProgress heights (replace_Znth (i) (((Znth j left_values_2 0) + 1 )) (left_values_2)) i ((j - 1 ) + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_6_1_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values_2 0) + 1 ) > (Znth i left_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (ChoirLeftInnerProgress heights (replace_Znth (i) (((Znth j left_values_2 0) + 1 )) (left_values_2)) i ((j - 1 ) + 1 ) )
.

Definition choir_singing_entail_wit_6_2 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) >= (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i ((j - 1 ) + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) >= (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  TT && emp 
|--
  “ (ChoirLeftInnerProgress heights left_values_2 i ((j - 1 ) + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_6_2_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) >= (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (ChoirLeftInnerProgress heights left_values_2 i ((j - 1 ) + 1 ) )
.

Definition choir_singing_entail_wit_6_3 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values_2 0) + 1 ) <= (Znth i left_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= (j - 1 )) ” 
  &&  “ ((j - 1 ) < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i ((j - 1 ) + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values_2 0) + 1 ) <= (Znth i left_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  TT && emp 
|--
  “ (ChoirLeftInnerProgress heights left_values_2 i ((j - 1 ) + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_6_3_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values_2 0) + 1 ) <= (Znth i left_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (ChoirLeftInnerProgress heights left_values_2 i ((j - 1 ) + 1 ) )
.

Definition choir_singing_entail_wit_7 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((-1) <= j)) (PreH8 : (j < i)) (PreH9 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH10 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values (i + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((-1) <= j)) (PreH8 : (j < i)) (PreH9 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH10 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  TT && emp 
|--
  “ (ChoirDPLeftPrefix heights left_values_2 (i + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_7_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((-1) <= j)) (PreH8 : (j < i)) (PreH9 : (ChoirLeftInnerProgress heights left_values_2 i (j + 1 ) )) (PreH10 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (ChoirDPLeftPrefix heights left_values_2 (i + 1 ) )
.

Definition choir_singing_entail_wit_8 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (i: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values_2 (i + 1 ) )) (PreH7 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values (i + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_entail_wit_9 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 i )) (PreH8 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 i )) (PreH8 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  TT && emp 
|--
  “ (ChoirDPLeftPrefix heights left_values_2 numsSize_pre ) ”
  &&  emp
).

Definition choir_singing_entail_wit_9_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 i )) (PreH8 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )
.

Definition choir_singing_entail_wit_10 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH5 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= ((numsSize_pre - 1 ) + 1 )) ” 
  &&  “ (((numsSize_pre - 1 ) + 1 ) <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values ((numsSize_pre - 1 ) + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH5 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  TT && emp 
|--
  “ (ChoirDPRightSuffix heights right_values_2 ((numsSize_pre - 1 ) + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_10_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH5 : (ChoirOnesFull right_values_2 numsSize_pre )) ,
  (ChoirDPRightSuffix heights right_values_2 ((numsSize_pre - 1 ) + 1 ) )
.

Definition choir_singing_entail_wit_11 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= (i + 1 ))) (PreH6 : ((i + 1 ) <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH8 : (ChoirDPRightSuffix heights right_values_2 (i + 1 ) )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i (i + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= (i + 1 ))) (PreH6 : ((i + 1 ) <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH8 : (ChoirDPRightSuffix heights right_values_2 (i + 1 ) )) ,
  TT && emp 
|--
  “ (ChoirRightInnerProgress heights right_values_2 i (i + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_11_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i >= 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= (i + 1 ))) (PreH6 : ((i + 1 ) <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH8 : (ChoirDPRightSuffix heights right_values_2 (i + 1 ) )) ,
  (ChoirRightInnerProgress heights right_values_2 i (i + 1 ) )
.

Definition choir_singing_entail_wit_12_1 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values_2 0) + 1 ) > (Znth i right_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  (IntArray.full dp_right_pre numsSize_pre (replace_Znth (i) (((Znth j right_values_2 0) + 1 )) (right_values_2)) )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i (j + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values_2 0) + 1 ) > (Znth i right_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  TT && emp 
|--
  “ (ChoirRightInnerProgress heights (replace_Znth (i) (((Znth j right_values_2 0) + 1 )) (right_values_2)) i (j + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_12_1_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values_2 0) + 1 ) > (Znth i right_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  (ChoirRightInnerProgress heights (replace_Znth (i) (((Znth j right_values_2 0) + 1 )) (right_values_2)) i (j + 1 ) )
.

Definition choir_singing_entail_wit_12_2 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) >= (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i (j + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) >= (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  TT && emp 
|--
  “ (ChoirRightInnerProgress heights right_values_2 i (j + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_12_2_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) >= (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  (ChoirRightInnerProgress heights right_values_2 i (j + 1 ) )
.

Definition choir_singing_entail_wit_12_3 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values_2 0) + 1 ) <= (Znth i right_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i (j + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values_2 0) + 1 ) <= (Znth i right_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  TT && emp 
|--
  “ (ChoirRightInnerProgress heights right_values_2 i (j + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_12_3_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values_2 0) + 1 ) <= (Znth i right_values_2 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  (ChoirRightInnerProgress heights right_values_2 i (j + 1 ) )
.

Definition choir_singing_entail_wit_13 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH10 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values i ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH10 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  TT && emp 
|--
  “ (ChoirDPRightSuffix heights right_values_2 i ) ”
  &&  emp
).

Definition choir_singing_entail_wit_13_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH10 : (ChoirRightInnerProgress heights right_values_2 i j )) ,
  (ChoirDPRightSuffix heights right_values_2 i )
.

Definition choir_singing_entail_wit_14 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (i: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH7 : (ChoirDPRightSuffix heights right_values_2 i )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= ((i - 1 ) + 1 )) ” 
  &&  “ (((i - 1 ) + 1 ) <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values ((i - 1 ) + 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (i: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH7 : (ChoirDPRightSuffix heights right_values_2 i )) ,
  TT && emp 
|--
  “ (ChoirDPRightSuffix heights right_values_2 ((i - 1 ) + 1 ) ) ”
  &&  emp
).

Definition choir_singing_entail_wit_14_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (i: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (0 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH7 : (ChoirDPRightSuffix heights right_values_2 i )) ,
  (ChoirDPRightSuffix heights right_values_2 ((i - 1 ) + 1 ) )
.

Definition choir_singing_entail_wit_15 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= (i + 1 ))) (PreH6 : ((i + 1 ) <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH8 : (ChoirDPRightSuffix heights right_values_2 (i + 1 ) )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= (i + 1 ))) (PreH6 : ((i + 1 ) <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH8 : (ChoirDPRightSuffix heights right_values_2 (i + 1 ) )) ,
  TT && emp 
|--
  “ (ChoirDPRightSuffix heights right_values_2 0 ) ”
  &&  emp
).

Definition choir_singing_entail_wit_15_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (i: Z) (PreH1 : (i < 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= (i + 1 ))) (PreH6 : ((i + 1 ) <= numsSize_pre)) (PreH7 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH8 : (ChoirDPRightSuffix heights right_values_2 (i + 1 ) )) ,
  (ChoirDPRightSuffix heights right_values_2 0 )
.

Definition choir_singing_entail_wit_16 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH5 : (ChoirDPRightSuffix heights right_values_2 0 )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ” 
  &&  “ (ChoirBestPrefix heights 0 0 ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH5 : (ChoirDPRightSuffix heights right_values_2 0 )) ,
  TT && emp 
|--
  “ (ChoirBestPrefix heights 0 0 ) ”
  &&  emp
).

Definition choir_singing_entail_wit_16_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH5 : (ChoirDPRightSuffix heights right_values_2 0 )) ,
  (ChoirBestPrefix heights 0 0 )
.

Definition choir_singing_entail_wit_17_1 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= numsSize_pre) ” 
  &&  “ (0 <= (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) - 1 )) ” 
  &&  “ ((((Znth k left_values_2 0) + (Znth k right_values_2 0) ) - 1 ) <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ” 
  &&  “ (ChoirBestPrefix heights (k + 1 ) (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) - 1 ) ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  TT && emp 
|--
  “ (ChoirBestPrefix heights (k + 1 ) (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) - 1 ) ) ” 
  &&  “ ((((Znth k left_values_2 0) + (Znth k right_values_2 0) ) - 1 ) <= numsSize_pre) ”
  &&  emp
).

Definition choir_singing_entail_wit_17_1_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (ChoirBestPrefix heights (k + 1 ) (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) - 1 ) )
.

Definition choir_singing_entail_wit_17_1_split_goal_2 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  ((((Znth k left_values_2 0) + (Znth k right_values_2 0) ) - 1 ) <= numsSize_pre)
.

Definition choir_singing_entail_wit_17_2 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) <= max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= numsSize_pre) ” 
  &&  “ (0 <= max_choir) ” 
  &&  “ (max_choir <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ” 
  &&  “ (ChoirBestPrefix heights (k + 1 ) max_choir ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) <= max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  TT && emp 
|--
  “ (ChoirBestPrefix heights (k + 1 ) max_choir ) ”
  &&  emp
).

Definition choir_singing_entail_wit_17_2_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values_2 0) + (Znth k right_values_2 0) ) <= max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (ChoirBestPrefix heights (k + 1 ) max_choir )
.

Definition choir_singing_entail_wit_18 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (1 <= max_choir) ” 
  &&  “ (max_choir <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ” 
  &&  “ (ChoirBestPrefix heights numsSize_pre max_choir ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  TT && emp 
|--
  “ (ChoirBestPrefix heights numsSize_pre max_choir ) ” 
  &&  “ (1 <= max_choir) ”
  &&  emp
).

Definition choir_singing_entail_wit_18_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  (ChoirBestPrefix heights numsSize_pre max_choir )
.

Definition choir_singing_entail_wit_18_split_goal_2 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (right_values_2: (@list Z)) (left_values_2: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  (1 <= max_choir)
.

Definition choir_singing_return_wit_1 := 
(
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (max_choir: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (1 <= max_choir)) (PreH5 : (max_choir <= numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH7 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH8 : (ChoirBestPrefix heights numsSize_pre max_choir )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values_2 )
  **  (IntArray.full dp_right_pre numsSize_pre right_values_2 )
|--
  EX (right_values: (@list Z))  (left_values: (@list Z)) ,
  “ (ChoirMinimumRemovals heights (numsSize_pre - max_choir ) ) ” 
  &&  “ (0 <= (numsSize_pre - max_choir )) ” 
  &&  “ ((numsSize_pre - max_choir ) < numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ”
  &&  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
) \/
(
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (max_choir: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (1 <= max_choir)) (PreH5 : (max_choir <= numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH7 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH8 : (ChoirBestPrefix heights numsSize_pre max_choir )) ,
  TT && emp 
|--
  “ (ChoirMinimumRemovals heights (numsSize_pre - max_choir ) ) ”
  &&  emp
).

Definition choir_singing_return_wit_1_split_goal_1 := 
forall (numsSize_pre: Z) (heights: (@list Z)) (left_values_2: (@list Z)) (right_values_2: (@list Z)) (max_choir: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100)) (PreH3 : ((Zlength (heights)) = numsSize_pre)) (PreH4 : (1 <= max_choir)) (PreH5 : (max_choir <= numsSize_pre)) (PreH6 : (ChoirDPLeftPrefix heights left_values_2 numsSize_pre )) (PreH7 : (ChoirDPRightSuffix heights right_values_2 0 )) (PreH8 : (ChoirBestPrefix heights numsSize_pre max_choir )) ,
  (ChoirMinimumRemovals heights (numsSize_pre - max_choir ) )
.

Definition choir_singing_partial_solve_wit_1 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_written: (@list Z)) (left_written: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written i )) (PreH8 : (ChoirOnesPrefix right_written i )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.seg dp_left_pre 0 i left_written )
  **  (IntArray.undef_seg dp_left_pre i numsSize_pre )
  **  (IntArray.seg dp_right_pre 0 i right_written )
  **  (IntArray.undef_seg dp_right_pre i numsSize_pre )
|--
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (ChoirOnesPrefix left_written i ) ” 
  &&  “ (ChoirOnesPrefix right_written i ) ”
  &&  (((dp_left_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_left_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.seg dp_left_pre 0 i left_written )
  **  (IntArray.seg dp_right_pre 0 i right_written )
  **  (IntArray.undef_seg dp_right_pre i numsSize_pre )
.

Definition choir_singing_partial_solve_wit_2 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_written: (@list Z)) (left_written: (@list Z)) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (ChoirOnesPrefix left_written i )) (PreH8 : (ChoirOnesPrefix right_written i )) ,
  (IntArray.seg dp_left_pre 0 (i + 1 ) (app (left_written) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_left_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.seg dp_right_pre 0 i right_written )
  **  (IntArray.undef_seg dp_right_pre i numsSize_pre )
|--
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (ChoirOnesPrefix left_written i ) ” 
  &&  “ (ChoirOnesPrefix right_written i ) ”
  &&  (((dp_right_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_right_pre (i + 1 ) numsSize_pre )
  **  (IntArray.seg dp_left_pre 0 (i + 1 ) (app (left_written) ((cons (1) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_left_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.seg dp_right_pre 0 i right_written )
.

Definition choir_singing_partial_solve_wit_3 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((-1) <= j)) (PreH8 : (j < i)) (PreH9 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH10 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (j >= 0) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= j) ” 
  &&  “ (j < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i (j + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j heights 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_partial_solve_wit_4 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (j >= 0)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((-1) <= j)) (PreH8 : (j < i)) (PreH9 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH10 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (j >= 0) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= j) ” 
  &&  “ (j < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i (j + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i heights 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_partial_solve_wit_5 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((Znth j heights 0) < (Znth i heights 0)) ” 
  &&  “ (j >= 0) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= j) ” 
  &&  “ (j < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i (j + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (((dp_left_pre + (j * sizeof(INT)))) # Int  |-> (Znth j left_values 0))
  **  (IntArray.missing_i dp_left_pre j 0 numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_partial_solve_wit_6 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j >= 0)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((-1) <= j)) (PreH9 : (j < i)) (PreH10 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH11 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((Znth j heights 0) < (Znth i heights 0)) ” 
  &&  “ (j >= 0) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= j) ” 
  &&  “ (j < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i (j + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (((dp_left_pre + (i * sizeof(INT)))) # Int  |-> (Znth i left_values 0))
  **  (IntArray.missing_i dp_left_pre i 0 numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_partial_solve_wit_7 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values 0) + 1 ) > (Znth i left_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (((Znth j left_values 0) + 1 ) > (Znth i left_values 0)) ” 
  &&  “ ((Znth j heights 0) < (Znth i heights 0)) ” 
  &&  “ (j >= 0) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= j) ” 
  &&  “ (j < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i (j + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (((dp_left_pre + (j * sizeof(INT)))) # Int  |-> (Znth j left_values 0))
  **  (IntArray.missing_i dp_left_pre j 0 numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_partial_solve_wit_8 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j left_values 0) + 1 ) > (Znth i left_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j >= 0)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((-1) <= j)) (PreH10 : (j < i)) (PreH11 : (ChoirLeftInnerProgress heights left_values i (j + 1 ) )) (PreH12 : (ChoirOnesFull right_values numsSize_pre )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (((Znth j left_values 0) + 1 ) > (Znth i left_values 0)) ” 
  &&  “ ((Znth j heights 0) < (Znth i heights 0)) ” 
  &&  “ (j >= 0) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((-1) <= j) ” 
  &&  “ (j < i) ” 
  &&  “ (ChoirLeftInnerProgress heights left_values i (j + 1 ) ) ” 
  &&  “ (ChoirOnesFull right_values numsSize_pre ) ”
  &&  (((dp_left_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dp_left_pre i 0 numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_partial_solve_wit_9 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH10 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i j ) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j heights 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_partial_solve_wit_10 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (j < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : ((i + 1 ) <= j)) (PreH8 : (j <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH10 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i j ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i heights 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_partial_solve_wit_11 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ ((Znth j heights 0) < (Znth i heights 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i j ) ”
  &&  (((dp_right_pre + (j * sizeof(INT)))) # Int  |-> (Znth j right_values 0))
  **  (IntArray.missing_i dp_right_pre j 0 numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
.

Definition choir_singing_partial_solve_wit_12 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : ((Znth j heights 0) < (Znth i heights 0))) (PreH2 : (j < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : ((i + 1 ) <= j)) (PreH9 : (j <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ ((Znth j heights 0) < (Znth i heights 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i j ) ”
  &&  (((dp_right_pre + (i * sizeof(INT)))) # Int  |-> (Znth i right_values 0))
  **  (IntArray.missing_i dp_right_pre i 0 numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
.

Definition choir_singing_partial_solve_wit_13 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values 0) + 1 ) > (Znth i right_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (((Znth j right_values 0) + 1 ) > (Znth i right_values 0)) ” 
  &&  “ ((Znth j heights 0) < (Znth i heights 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i j ) ”
  &&  (((dp_right_pre + (j * sizeof(INT)))) # Int  |-> (Znth j right_values 0))
  **  (IntArray.missing_i dp_right_pre j 0 numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
.

Definition choir_singing_partial_solve_wit_14 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (j: Z) (i: Z) (PreH1 : (((Znth j right_values 0) + 1 ) > (Znth i right_values 0))) (PreH2 : ((Znth j heights 0) < (Znth i heights 0))) (PreH3 : (j < numsSize_pre)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100)) (PreH6 : ((Zlength (heights)) = numsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : ((i + 1 ) <= j)) (PreH10 : (j <= numsSize_pre)) (PreH11 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH12 : (ChoirRightInnerProgress heights right_values i j )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
|--
  “ (((Znth j right_values 0) + 1 ) > (Znth i right_values 0)) ” 
  &&  “ ((Znth j heights 0) < (Znth i heights 0)) ” 
  &&  “ (j < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ ((i + 1 ) <= j) ” 
  &&  “ (j <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirRightInnerProgress heights right_values i j ) ”
  &&  (((dp_right_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dp_right_pre i 0 numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
.

Definition choir_singing_partial_solve_wit_15 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (k < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= numsSize_pre) ” 
  &&  “ (0 <= max_choir) ” 
  &&  “ (max_choir <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ” 
  &&  “ (ChoirBestPrefix heights k max_choir ) ”
  &&  (((dp_left_pre + (k * sizeof(INT)))) # Int  |-> (Znth k left_values 0))
  **  (IntArray.missing_i dp_left_pre k 0 numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
.

Definition choir_singing_partial_solve_wit_16 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (k < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100)) (PreH4 : ((Zlength (heights)) = numsSize_pre)) (PreH5 : (0 <= k)) (PreH6 : (k <= numsSize_pre)) (PreH7 : (0 <= max_choir)) (PreH8 : (max_choir <= numsSize_pre)) (PreH9 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH10 : (ChoirDPRightSuffix heights right_values 0 )) (PreH11 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
|--
  “ (k < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= numsSize_pre) ” 
  &&  “ (0 <= max_choir) ” 
  &&  “ (max_choir <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ” 
  &&  “ (ChoirBestPrefix heights k max_choir ) ”
  &&  (((dp_right_pre + (k * sizeof(INT)))) # Int  |-> (Znth k right_values 0))
  **  (IntArray.missing_i dp_right_pre k 0 numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
.

Definition choir_singing_partial_solve_wit_17 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir) ” 
  &&  “ (k < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= numsSize_pre) ” 
  &&  “ (0 <= max_choir) ” 
  &&  “ (max_choir <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ” 
  &&  “ (ChoirBestPrefix heights k max_choir ) ”
  &&  (((dp_left_pre + (k * sizeof(INT)))) # Int  |-> (Znth k left_values 0))
  **  (IntArray.missing_i dp_left_pre k 0 numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
.

Definition choir_singing_partial_solve_wit_18 := 
forall (dp_right_pre: Z) (dp_left_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (heights: (@list Z)) (right_values: (@list Z)) (left_values: (@list Z)) (max_choir: Z) (k: Z) (PreH1 : (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir)) (PreH2 : (k < numsSize_pre)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100)) (PreH5 : ((Zlength (heights)) = numsSize_pre)) (PreH6 : (0 <= k)) (PreH7 : (k <= numsSize_pre)) (PreH8 : (0 <= max_choir)) (PreH9 : (max_choir <= numsSize_pre)) (PreH10 : (ChoirDPLeftPrefix heights left_values numsSize_pre )) (PreH11 : (ChoirDPRightSuffix heights right_values 0 )) (PreH12 : (ChoirBestPrefix heights k max_choir )) ,
  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full dp_right_pre numsSize_pre right_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
|--
  “ (((Znth k left_values 0) + (Znth k right_values 0) ) > max_choir) ” 
  &&  “ (k < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100) ” 
  &&  “ ((Zlength (heights)) = numsSize_pre) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= numsSize_pre) ” 
  &&  “ (0 <= max_choir) ” 
  &&  “ (max_choir <= numsSize_pre) ” 
  &&  “ (ChoirDPLeftPrefix heights left_values numsSize_pre ) ” 
  &&  “ (ChoirDPRightSuffix heights right_values 0 ) ” 
  &&  “ (ChoirBestPrefix heights k max_choir ) ”
  &&  (((dp_right_pre + (k * sizeof(INT)))) # Int  |-> (Znth k right_values 0))
  **  (IntArray.missing_i dp_right_pre k 0 numsSize_pre right_values )
  **  (IntArray.full dp_left_pre numsSize_pre left_values )
  **  (IntArray.full nums_pre numsSize_pre heights )
.

Module Type VC_Correct.


Axiom proof_of_choir_singing_safety_wit_1 : choir_singing_safety_wit_1.
Axiom proof_of_choir_singing_safety_wit_2 : choir_singing_safety_wit_2.
Axiom proof_of_choir_singing_safety_wit_3 : choir_singing_safety_wit_3.
Axiom proof_of_choir_singing_safety_wit_4 : choir_singing_safety_wit_4.
Axiom proof_of_choir_singing_safety_wit_5 : choir_singing_safety_wit_5.
Axiom proof_of_choir_singing_safety_wit_6 : choir_singing_safety_wit_6.
Axiom proof_of_choir_singing_safety_wit_7 : choir_singing_safety_wit_7.
Axiom proof_of_choir_singing_safety_wit_8 : choir_singing_safety_wit_8.
Axiom proof_of_choir_singing_safety_wit_9 : choir_singing_safety_wit_9.
Axiom proof_of_choir_singing_safety_wit_10 : choir_singing_safety_wit_10.
Axiom proof_of_choir_singing_safety_wit_11 : choir_singing_safety_wit_11.
Axiom proof_of_choir_singing_safety_wit_12 : choir_singing_safety_wit_12.
Axiom proof_of_choir_singing_safety_wit_13 : choir_singing_safety_wit_13.
Axiom proof_of_choir_singing_safety_wit_14 : choir_singing_safety_wit_14.
Axiom proof_of_choir_singing_safety_wit_15 : choir_singing_safety_wit_15.
Axiom proof_of_choir_singing_safety_wit_16 : choir_singing_safety_wit_16.
Axiom proof_of_choir_singing_safety_wit_17 : choir_singing_safety_wit_17.
Axiom proof_of_choir_singing_safety_wit_18 : choir_singing_safety_wit_18.
Axiom proof_of_choir_singing_safety_wit_19 : choir_singing_safety_wit_19.
Axiom proof_of_choir_singing_safety_wit_20 : choir_singing_safety_wit_20.
Axiom proof_of_choir_singing_safety_wit_21 : choir_singing_safety_wit_21.
Axiom proof_of_choir_singing_safety_wit_22 : choir_singing_safety_wit_22.
Axiom proof_of_choir_singing_safety_wit_23 : choir_singing_safety_wit_23.
Axiom proof_of_choir_singing_safety_wit_24 : choir_singing_safety_wit_24.
Axiom proof_of_choir_singing_safety_wit_25 : choir_singing_safety_wit_25.
Axiom proof_of_choir_singing_safety_wit_26 : choir_singing_safety_wit_26.
Axiom proof_of_choir_singing_safety_wit_27 : choir_singing_safety_wit_27.
Axiom proof_of_choir_singing_safety_wit_28 : choir_singing_safety_wit_28.
Axiom proof_of_choir_singing_safety_wit_29 : choir_singing_safety_wit_29.
Axiom proof_of_choir_singing_safety_wit_30 : choir_singing_safety_wit_30.
Axiom proof_of_choir_singing_safety_wit_31 : choir_singing_safety_wit_31.
Axiom proof_of_choir_singing_safety_wit_32 : choir_singing_safety_wit_32.
Axiom proof_of_choir_singing_safety_wit_33 : choir_singing_safety_wit_33.
Axiom proof_of_choir_singing_safety_wit_34 : choir_singing_safety_wit_34.
Axiom proof_of_choir_singing_safety_wit_35 : choir_singing_safety_wit_35.
Axiom proof_of_choir_singing_safety_wit_36 : choir_singing_safety_wit_36.
Axiom proof_of_choir_singing_safety_wit_37 : choir_singing_safety_wit_37.
Axiom proof_of_choir_singing_safety_wit_38 : choir_singing_safety_wit_38.
Axiom proof_of_choir_singing_entail_wit_1 : choir_singing_entail_wit_1.
Axiom proof_of_choir_singing_entail_wit_2 : choir_singing_entail_wit_2.
Axiom proof_of_choir_singing_entail_wit_3 : choir_singing_entail_wit_3.
Axiom proof_of_choir_singing_entail_wit_4 : choir_singing_entail_wit_4.
Axiom proof_of_choir_singing_entail_wit_5 : choir_singing_entail_wit_5.
Axiom proof_of_choir_singing_entail_wit_6_1 : choir_singing_entail_wit_6_1.
Axiom proof_of_choir_singing_entail_wit_6_2 : choir_singing_entail_wit_6_2.
Axiom proof_of_choir_singing_entail_wit_6_3 : choir_singing_entail_wit_6_3.
Axiom proof_of_choir_singing_entail_wit_7 : choir_singing_entail_wit_7.
Axiom proof_of_choir_singing_entail_wit_8 : choir_singing_entail_wit_8.
Axiom proof_of_choir_singing_entail_wit_9 : choir_singing_entail_wit_9.
Axiom proof_of_choir_singing_entail_wit_10 : choir_singing_entail_wit_10.
Axiom proof_of_choir_singing_entail_wit_11 : choir_singing_entail_wit_11.
Axiom proof_of_choir_singing_entail_wit_12_1 : choir_singing_entail_wit_12_1.
Axiom proof_of_choir_singing_entail_wit_12_2 : choir_singing_entail_wit_12_2.
Axiom proof_of_choir_singing_entail_wit_12_3 : choir_singing_entail_wit_12_3.
Axiom proof_of_choir_singing_entail_wit_13 : choir_singing_entail_wit_13.
Axiom proof_of_choir_singing_entail_wit_14 : choir_singing_entail_wit_14.
Axiom proof_of_choir_singing_entail_wit_15 : choir_singing_entail_wit_15.
Axiom proof_of_choir_singing_entail_wit_16 : choir_singing_entail_wit_16.
Axiom proof_of_choir_singing_entail_wit_17_1 : choir_singing_entail_wit_17_1.
Axiom proof_of_choir_singing_entail_wit_17_2 : choir_singing_entail_wit_17_2.
Axiom proof_of_choir_singing_entail_wit_18 : choir_singing_entail_wit_18.
Axiom proof_of_choir_singing_return_wit_1 : choir_singing_return_wit_1.
Axiom proof_of_choir_singing_partial_solve_wit_1 : choir_singing_partial_solve_wit_1.
Axiom proof_of_choir_singing_partial_solve_wit_2 : choir_singing_partial_solve_wit_2.
Axiom proof_of_choir_singing_partial_solve_wit_3 : choir_singing_partial_solve_wit_3.
Axiom proof_of_choir_singing_partial_solve_wit_4 : choir_singing_partial_solve_wit_4.
Axiom proof_of_choir_singing_partial_solve_wit_5 : choir_singing_partial_solve_wit_5.
Axiom proof_of_choir_singing_partial_solve_wit_6 : choir_singing_partial_solve_wit_6.
Axiom proof_of_choir_singing_partial_solve_wit_7 : choir_singing_partial_solve_wit_7.
Axiom proof_of_choir_singing_partial_solve_wit_8 : choir_singing_partial_solve_wit_8.
Axiom proof_of_choir_singing_partial_solve_wit_9 : choir_singing_partial_solve_wit_9.
Axiom proof_of_choir_singing_partial_solve_wit_10 : choir_singing_partial_solve_wit_10.
Axiom proof_of_choir_singing_partial_solve_wit_11 : choir_singing_partial_solve_wit_11.
Axiom proof_of_choir_singing_partial_solve_wit_12 : choir_singing_partial_solve_wit_12.
Axiom proof_of_choir_singing_partial_solve_wit_13 : choir_singing_partial_solve_wit_13.
Axiom proof_of_choir_singing_partial_solve_wit_14 : choir_singing_partial_solve_wit_14.
Axiom proof_of_choir_singing_partial_solve_wit_15 : choir_singing_partial_solve_wit_15.
Axiom proof_of_choir_singing_partial_solve_wit_16 : choir_singing_partial_solve_wit_16.
Axiom proof_of_choir_singing_partial_solve_wit_17 : choir_singing_partial_solve_wit_17.
Axiom proof_of_choir_singing_partial_solve_wit_18 : choir_singing_partial_solve_wit_18.

End VC_Correct.
