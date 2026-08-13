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
Require Import SimpleC.EE.LLM_bench.Algorithms.max_sum_increasing_sequence.max_sum_increasing_sequence_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function maxSumIncreasingSequence -----*)

Definition maxSumIncreasingSequence_safety_wit_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSumIncreasingSequence_safety_wit_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSumIncreasingSequence_safety_wit_3 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  (((dp_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg dp_pre 1 numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSumIncreasingSequence_safety_wit_4 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "ans" ) )) # Int  |-> (Znth 0 l 0))
  **  (((dp_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg dp_pre 1 numsSize_pre )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition maxSumIncreasingSequence_safety_wit_5 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.seg dp_pre 0 (i + 1 ) (app (d) ((cons ((Znth i l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSumIncreasingSequence_safety_wit_6 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (((Znth (j - 0 ) d 0) + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) d 0) + (Znth i l 0) )) ”
) \/
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (((Znth (j - 0 ) d 0) + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (j - 0 ) d 0) + (Znth i l 0) )) ”
).

Definition maxSumIncreasingSequence_safety_wit_6_split_goal_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (((Znth (j - 0 ) d 0) + (Znth i l 0) ) <= INT_MAX) ”
.

Definition maxSumIncreasingSequence_safety_wit_6_split_goal_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "candidate" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((INT_MIN) <= ((Znth (j - 0 ) d 0) + (Znth i l 0) )) ”
.

Definition maxSumIncreasingSequence_safety_wit_7 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d 0) + (Znth i l 0) ) > (Znth (i - 0 ) d 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= (i * 10000 ))) (PreH13 : (MSISBestSoFar l i ans )) (PreH14 : (MSISInnerProgress l d i j )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full dp_pre (i + 1 ) (replace_Znth (i) (((Znth (j - 0 ) d 0) + (Znth i l 0) )) (d)) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition maxSumIncreasingSequence_safety_wit_8 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d 0) + (Znth i l 0) ) <= (Znth (i - 0 ) d 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= (i * 10000 ))) (PreH13 : (MSISBestSoFar l i ans )) (PreH14 : (MSISInnerProgress l d i j )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition maxSumIncreasingSequence_safety_wit_9 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) >= (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition maxSumIncreasingSequence_safety_wit_10 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d (i + 1 ) )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> (Znth (i - 0 ) d 0))
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition maxSumIncreasingSequence_safety_wit_11 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d 0) <= ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d (i + 1 ) )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "numsSize" ) )) # Int  |-> numsSize_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition maxSumIncreasingSequence_entail_wit_1 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (((dp_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg dp_pre 1 numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (1 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) <= (1 * 10000 )) ” 
  &&  “ (MSISDPTablePrefix l d 1 ) ” 
  &&  “ (MSISBestSoFar l 1 (Znth 0 l 0) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 1 d )
  **  (IntArray.undef_seg dp_pre 1 numsSize_pre )
) \/
(
forall (dp_pre: Z) (numsSize_pre: Z) (l: (@list Z)) (PreH1 : ((Znth 0 l 0) <= INT_MAX)) (PreH2 : ((Znth 0 l 0) >= INT_MIN)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (((dp_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (1 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) <= (1 * 10000 )) ” 
  &&  “ (MSISDPTablePrefix l d 1 ) ” 
  &&  “ (MSISBestSoFar l 1 (Znth 0 l 0) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.seg dp_pre 0 1 d )
).

Definition maxSumIncreasingSequence_entail_wit_2 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d_2 i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) (app (d_2) ((cons ((Znth i l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d_2 i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ” 
  &&  “ (MSISInnerProgress l (app (d_2) ((cons ((Znth i l 0)) ((@nil Z))))) i 0 ) ”
  &&  emp
).

Definition maxSumIncreasingSequence_entail_wit_2_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d_2 i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))
.

Definition maxSumIncreasingSequence_entail_wit_2_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d_2 i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (MSISInnerProgress l (app (d_2) ((cons ((Znth i l 0)) ((@nil Z))))) i 0 )
.

Definition maxSumIncreasingSequence_entail_wit_3_1 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + (Znth i l 0) ) > (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= (i * 10000 ))) (PreH13 : (MSISBestSoFar l i ans )) (PreH14 : (MSISInnerProgress l d_2 i j )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full dp_pre (i + 1 ) (replace_Znth (i) (((Znth (j - 0 ) d_2 0) + (Znth i l 0) )) (d_2)) )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (dp_pre: Z) (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + (Znth i l 0) ) > (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= (i * 10000 ))) (PreH13 : (MSISBestSoFar l i ans )) (PreH14 : (MSISInnerProgress l d_2 i j )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full dp_pre (i + 1 ) (replace_Znth (i) (((Znth (j - 0 ) d_2 0) + (Znth i l 0) )) (d_2)) )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.seg dp_pre 0 (i + 1 ) d )
).

Definition maxSumIncreasingSequence_entail_wit_3_2 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + (Znth i l 0) ) <= (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= (i * 10000 ))) (PreH13 : (MSISBestSoFar l i ans )) (PreH14 : (MSISInnerProgress l d_2 i j )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + (Znth i l 0) ) <= (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= (i * 10000 ))) (PreH13 : (MSISBestSoFar l i ans )) (PreH14 : (MSISInnerProgress l d_2 i j )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (MSISInnerProgress l d_2 i (j + 1 ) ) ”
  &&  emp
).

Definition maxSumIncreasingSequence_entail_wit_3_2_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d_2 0) + (Znth i l 0) ) <= (Znth (i - 0 ) d_2 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= (i * 10000 ))) (PreH13 : (MSISBestSoFar l i ans )) (PreH14 : (MSISInnerProgress l d_2 i j )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (MSISInnerProgress l d_2 i (j + 1 ) )
.

Definition maxSumIncreasingSequence_entail_wit_3_3 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) >= (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d_2 i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) >= (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d_2 i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (MSISInnerProgress l d_2 i (j + 1 ) ) ”
  &&  emp
).

Definition maxSumIncreasingSequence_entail_wit_3_3_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) >= (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d_2 i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (MSISInnerProgress l d_2 i (j + 1 ) )
.

Definition maxSumIncreasingSequence_entail_wit_4 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= (i * 10000 ))) (PreH11 : (MSISBestSoFar l i ans )) (PreH12 : (MSISInnerProgress l d_2 i j )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISDPTablePrefix l d (i + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= (i * 10000 ))) (PreH11 : (MSISBestSoFar l i ans )) (PreH12 : (MSISInnerProgress l d_2 i j )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ” 
  &&  “ (MSISDPTablePrefix l d_2 (i + 1 ) ) ”
  &&  emp
).

Definition maxSumIncreasingSequence_entail_wit_4_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= (i * 10000 ))) (PreH11 : (MSISBestSoFar l i ans )) (PreH12 : (MSISInnerProgress l d_2 i j )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))
.

Definition maxSumIncreasingSequence_entail_wit_4_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j >= i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= (i * 10000 ))) (PreH11 : (MSISBestSoFar l i ans )) (PreH12 : (MSISInnerProgress l d_2 i j )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (MSISDPTablePrefix l d_2 (i + 1 ) )
.

Definition maxSumIncreasingSequence_entail_wit_5_1 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d_2 (i + 1 ) )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (1 <= (Znth (i - 0 ) d_2 0)) ” 
  &&  “ ((Znth (i - 0 ) d_2 0) <= ((i + 1 ) * 10000 )) ” 
  &&  “ (MSISDPTablePrefix l d (i + 1 ) ) ” 
  &&  “ (MSISBestSoFar l (i + 1 ) (Znth (i - 0 ) d_2 0) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d_2 (i + 1 ) )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ” 
  &&  “ (MSISBestSoFar l (i + 1 ) (Znth (i - 0 ) d_2 0) ) ” 
  &&  “ ((Znth (i - 0 ) d_2 0) <= ((i + 1 ) * 10000 )) ”
  &&  emp
).

Definition maxSumIncreasingSequence_entail_wit_5_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d_2 (i + 1 ) )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))
.

Definition maxSumIncreasingSequence_entail_wit_5_1_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d_2 (i + 1 ) )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (MSISBestSoFar l (i + 1 ) (Znth (i - 0 ) d_2 0) )
.

Definition maxSumIncreasingSequence_entail_wit_5_1_split_goal_3 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d_2 (i + 1 ) )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  ((Znth (i - 0 ) d_2 0) <= ((i + 1 ) * 10000 ))
.

Definition maxSumIncreasingSequence_entail_wit_5_2 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) <= ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d_2 (i + 1 ) )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d_2 )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= ((i + 1 ) * 10000 )) ” 
  &&  “ (MSISDPTablePrefix l d (i + 1 ) ) ” 
  &&  “ (MSISBestSoFar l (i + 1 ) ans ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) <= ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d_2 (i + 1 ) )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ” 
  &&  “ (MSISBestSoFar l (i + 1 ) ans ) ”
  &&  emp
).

Definition maxSumIncreasingSequence_entail_wit_5_2_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) <= ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d_2 (i + 1 ) )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))
.

Definition maxSumIncreasingSequence_entail_wit_5_2_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d_2 0) <= ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d_2 (i + 1 ) )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < numsSize_pre)) -> ((1 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (MSISBestSoFar l (i + 1 ) ans )
.

Definition maxSumIncreasingSequence_return_wit_1 := 
(
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d_2 i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d_2 )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
|--
  EX (d: (@list Z)) ,
  “ (MSISMaximum l ans ) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= INT_MAX) ” 
  &&  “ (MSISDPTablePrefix l d numsSize_pre ) ”
  &&  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.full dp_pre numsSize_pre d )
) \/
(
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d_2 i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (MSISDPTablePrefix l d_2 numsSize_pre ) ” 
  &&  “ (MSISMaximum l ans ) ”
  &&  emp
).

Definition maxSumIncreasingSequence_return_wit_1_split_goal_1 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d_2 i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (MSISDPTablePrefix l d_2 numsSize_pre )
.

Definition maxSumIncreasingSequence_return_wit_1_split_goal_2 := 
forall (numsSize_pre: Z) (l: (@list Z)) (d_2: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i >= numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d_2 i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (MSISMaximum l ans )
.

Definition maxSumIncreasingSequence_partial_solve_wit_1 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((nums_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i nums_pre 0 0 numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_2 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_full dp_pre numsSize_pre )
|--
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((dp_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre 1 numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
.

Definition maxSumIncreasingSequence_partial_solve_wit_3 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (((dp_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg dp_pre 1 numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
|--
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((nums_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i nums_pre 0 0 numsSize_pre l )
  **  (((dp_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg dp_pre 1 numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_4 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
|--
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISDPTablePrefix l d i ) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_5 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (i: Z) (PreH1 : (i < numsSize_pre)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i <= numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISDPTablePrefix l d i )) (PreH10 : (MSISBestSoFar l i ans )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
  **  (IntArray.undef_seg dp_pre i numsSize_pre )
|--
  “ (i < numsSize_pre) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISDPTablePrefix l d i ) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 i d )
.

Definition maxSumIncreasingSequence_partial_solve_wit_6 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= (i * 10000 ))) (PreH11 : (MSISBestSoFar l i ans )) (PreH12 : (MSISInnerProgress l d i j )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((nums_pre + (j * sizeof(INT)))) # Int  |-> (Znth j l 0))
  **  (IntArray.missing_i nums_pre j 0 numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_7 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (j < i)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (0 <= j)) (PreH8 : (j <= i)) (PreH9 : (1 <= ans)) (PreH10 : (ans <= (i * 10000 ))) (PreH11 : (MSISBestSoFar l i ans )) (PreH12 : (MSISInnerProgress l d i j )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_8 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((dp_pre + (j * sizeof(INT)))) # Int  |-> (Znth (j - 0 ) d 0))
  **  (IntArray.missing_i dp_pre j 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_9 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_10 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : ((Znth j l 0) < (Znth i l 0))) (PreH2 : (j < i)) (PreH3 : (1 <= numsSize_pre)) (PreH4 : (numsSize_pre <= 100000)) (PreH5 : ((Zlength (l)) = numsSize_pre)) (PreH6 : (1 <= i)) (PreH7 : (i < numsSize_pre)) (PreH8 : (0 <= j)) (PreH9 : (j <= i)) (PreH10 : (1 <= ans)) (PreH11 : (ans <= (i * 10000 ))) (PreH12 : (MSISBestSoFar l i ans )) (PreH13 : (MSISInnerProgress l d i j )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) d 0))
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_11 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (ans: Z) (j: Z) (i: Z) (PreH1 : (((Znth (j - 0 ) d 0) + (Znth i l 0) ) > (Znth (i - 0 ) d 0))) (PreH2 : ((Znth j l 0) < (Znth i l 0))) (PreH3 : (j < i)) (PreH4 : (1 <= numsSize_pre)) (PreH5 : (numsSize_pre <= 100000)) (PreH6 : ((Zlength (l)) = numsSize_pre)) (PreH7 : (1 <= i)) (PreH8 : (i < numsSize_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= i)) (PreH11 : (1 <= ans)) (PreH12 : (ans <= (i * 10000 ))) (PreH13 : (MSISBestSoFar l i ans )) (PreH14 : (MSISInnerProgress l d i j )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (((Znth (j - 0 ) d 0) + (Znth i l 0) ) > (Znth (i - 0 ) d 0)) ” 
  &&  “ ((Znth j l 0) < (Znth i l 0)) ” 
  &&  “ (j < i) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISInnerProgress l d i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_12 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : (1 <= numsSize_pre)) (PreH2 : (numsSize_pre <= 100000)) (PreH3 : ((Zlength (l)) = numsSize_pre)) (PreH4 : (1 <= i)) (PreH5 : (i < numsSize_pre)) (PreH6 : (1 <= ans)) (PreH7 : (ans <= (i * 10000 ))) (PreH8 : (MSISBestSoFar l i ans )) (PreH9 : (MSISDPTablePrefix l d (i + 1 ) )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISDPTablePrefix l d (i + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) d 0))
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Definition maxSumIncreasingSequence_partial_solve_wit_13 := 
forall (dp_pre: Z) (numsSize_pre: Z) (nums_pre: Z) (l: (@list Z)) (d: (@list Z)) (i: Z) (ans: Z) (PreH1 : ((Znth (i - 0 ) d 0) > ans)) (PreH2 : (1 <= numsSize_pre)) (PreH3 : (numsSize_pre <= 100000)) (PreH4 : ((Zlength (l)) = numsSize_pre)) (PreH5 : (1 <= i)) (PreH6 : (i < numsSize_pre)) (PreH7 : (1 <= ans)) (PreH8 : (ans <= (i * 10000 ))) (PreH9 : (MSISBestSoFar l i ans )) (PreH10 : (MSISDPTablePrefix l d (i + 1 ) )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
|--
  “ ((Znth (i - 0 ) d 0) > ans) ” 
  &&  “ (1 <= numsSize_pre) ” 
  &&  “ (numsSize_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = numsSize_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < numsSize_pre) ” 
  &&  “ (1 <= ans) ” 
  &&  “ (ans <= (i * 10000 )) ” 
  &&  “ (MSISBestSoFar l i ans ) ” 
  &&  “ (MSISDPTablePrefix l d (i + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < numsSize_pre)) -> ((1 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  (((dp_pre + (i * sizeof(INT)))) # Int  |-> (Znth (i - 0 ) d 0))
  **  (IntArray.missing_i dp_pre i 0 (i + 1 ) d )
  **  (IntArray.full nums_pre numsSize_pre l )
  **  (IntArray.undef_seg dp_pre (i + 1 ) numsSize_pre )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_maxSumIncreasingSequence_safety_wit_1 : maxSumIncreasingSequence_safety_wit_1.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_2 : maxSumIncreasingSequence_safety_wit_2.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_3 : maxSumIncreasingSequence_safety_wit_3.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_4 : maxSumIncreasingSequence_safety_wit_4.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_5 : maxSumIncreasingSequence_safety_wit_5.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_6 : maxSumIncreasingSequence_safety_wit_6.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_7 : maxSumIncreasingSequence_safety_wit_7.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_8 : maxSumIncreasingSequence_safety_wit_8.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_9 : maxSumIncreasingSequence_safety_wit_9.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_10 : maxSumIncreasingSequence_safety_wit_10.
Axiom proof_of_maxSumIncreasingSequence_safety_wit_11 : maxSumIncreasingSequence_safety_wit_11.
Axiom proof_of_maxSumIncreasingSequence_entail_wit_1 : maxSumIncreasingSequence_entail_wit_1.
Axiom proof_of_maxSumIncreasingSequence_entail_wit_2 : maxSumIncreasingSequence_entail_wit_2.
Axiom proof_of_maxSumIncreasingSequence_entail_wit_3_1 : maxSumIncreasingSequence_entail_wit_3_1.
Axiom proof_of_maxSumIncreasingSequence_entail_wit_3_2 : maxSumIncreasingSequence_entail_wit_3_2.
Axiom proof_of_maxSumIncreasingSequence_entail_wit_3_3 : maxSumIncreasingSequence_entail_wit_3_3.
Axiom proof_of_maxSumIncreasingSequence_entail_wit_4 : maxSumIncreasingSequence_entail_wit_4.
Axiom proof_of_maxSumIncreasingSequence_entail_wit_5_1 : maxSumIncreasingSequence_entail_wit_5_1.
Axiom proof_of_maxSumIncreasingSequence_entail_wit_5_2 : maxSumIncreasingSequence_entail_wit_5_2.
Axiom proof_of_maxSumIncreasingSequence_return_wit_1 : maxSumIncreasingSequence_return_wit_1.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_1 : maxSumIncreasingSequence_partial_solve_wit_1.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_2 : maxSumIncreasingSequence_partial_solve_wit_2.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_3 : maxSumIncreasingSequence_partial_solve_wit_3.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_4 : maxSumIncreasingSequence_partial_solve_wit_4.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_5 : maxSumIncreasingSequence_partial_solve_wit_5.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_6 : maxSumIncreasingSequence_partial_solve_wit_6.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_7 : maxSumIncreasingSequence_partial_solve_wit_7.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_8 : maxSumIncreasingSequence_partial_solve_wit_8.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_9 : maxSumIncreasingSequence_partial_solve_wit_9.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_10 : maxSumIncreasingSequence_partial_solve_wit_10.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_11 : maxSumIncreasingSequence_partial_solve_wit_11.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_12 : maxSumIncreasingSequence_partial_solve_wit_12.
Axiom proof_of_maxSumIncreasingSequence_partial_solve_wit_13 : maxSumIncreasingSequence_partial_solve_wit_13.

End VC_Correct.
