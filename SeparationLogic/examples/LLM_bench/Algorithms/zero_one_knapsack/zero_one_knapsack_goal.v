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
Require Import SimpleC.EE.LLM_bench.Algorithms.zero_one_knapsack.zero_one_knapsack_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function zeroOneKnapsack -----*)

Definition zeroOneKnapsack_safety_wit_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k weights_l 0)) /\ ((Znth k weights_l 0) <= (capacity_pre + 1 ))))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values_l 0)) /\ ((Znth k_2 values_l 0) <= 10000)))) ,
  ((( &( "width" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((capacity_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (capacity_pre + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_2 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k weights_l 0)) /\ ((Znth k weights_l 0) <= (capacity_pre + 1 ))))) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values_l 0)) /\ ((Znth k_2 values_l 0) <= 10000)))) ,
  ((( &( "width" ) )) # Int  |->_)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_3 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k weights_l 0)) /\ ((Znth k weights_l 0) <= (capacity_pre + 1 ))))) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values_l 0)) /\ ((Znth k_2 values_l 0) <= 10000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_4 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (width: Z) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (i * width ))) (PreH14 : ((i * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l i )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH18 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (i * width ) dp_l )
  **  (IntArray.undef_seg dp_pre (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_5 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH20 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * width ) + j )) ”
.

Definition zeroOneKnapsack_safety_wit_6 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH18 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH19 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH20 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((i * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * width )) ”
.

Definition zeroOneKnapsack_safety_wit_7 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (idx = ((i * width ) + j ))) (PreH15 : (0 <= idx)) (PreH16 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (0 <= idx)) (PreH19 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH21 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH22 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH23 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_8 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (i = 0)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (idx = ((i * width ) + j ))) (PreH16 : (0 <= idx)) (PreH17 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : (0 <= idx)) (PreH20 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_9 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (i <> 0)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (idx = ((i * width ) + j ))) (PreH16 : (0 <= idx)) (PreH17 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : (0 <= idx)) (PreH20 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_10 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH24 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_11 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH24 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "item" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_12 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH24 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "item" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_13 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH32 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "without" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((((i - 1 ) * width ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - 1 ) * width ) + j )) ”
.

Definition zeroOneKnapsack_safety_wit_14 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH32 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "without" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((i - 1 ) * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - 1 ) * width )) ”
.

Definition zeroOneKnapsack_safety_wit_15 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH32 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "without" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_16 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH32 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "without" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_17 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "without" ) )) # Int  |-> without)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((((i - 1 ) * width ) + (j - w ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - 1 ) * width ) + (j - w ) )) ”
.

Definition zeroOneKnapsack_safety_wit_18 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "without" ) )) # Int  |-> without)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((j - w ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - w )) ”
.

Definition zeroOneKnapsack_safety_wit_19 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "without" ) )) # Int  |-> without)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((i - 1 ) * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - 1 ) * width )) ”
.

Definition zeroOneKnapsack_safety_wit_20 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "without" ) )) # Int  |-> without)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_21 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "without" ) )) # Int  |-> without)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_22 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (0 <= prev)) (PreH32 : (prev <= 4000000)) (PreH33 : (INT_MIN <= (prev + v ))) (PreH34 : ((prev + v ) <= INT_MAX)) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH37 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH38 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH39 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH40 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "with_val" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "item" ) )) # Int  |-> item)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "v" ) )) # Int  |-> v)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "without" ) )) # Int  |-> without)
  **  ((( &( "prev" ) )) # Int  |-> prev)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((prev + v ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prev + v )) ”
.

Definition zeroOneKnapsack_safety_wit_23 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (idx = ((i * width ) + j ))) (PreH15 : (0 <= idx)) (PreH16 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) )) (PreH19 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH20 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH21 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_24 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l (i + 1 ) )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH14 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH15 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i + 1 ) * width ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i + 1 ) * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_25 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH11 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH12 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l (n_pre + 1 ) )) (PreH13 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) (PreH14 : (0 <= (Znth ((n_pre * width ) + capacity_pre ) dp_l 0))) (PreH15 : ((Znth ((n_pre * width ) + capacity_pre ) dp_l 0) <= 4000000)) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ (((n_pre * width ) + capacity_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre * width ) + capacity_pre )) ”
.

Definition zeroOneKnapsack_safety_wit_26 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH11 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH12 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l (n_pre + 1 ) )) (PreH13 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) (PreH14 : (0 <= (Znth ((n_pre * width ) + capacity_pre ) dp_l 0))) (PreH15 : ((Znth ((n_pre * width ) + capacity_pre ) dp_l 0) <= 4000000)) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ ((n_pre * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * width )) ”
.

Definition zeroOneKnapsack_entail_wit_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((1 <= (Znth k_3 weights_l 0)) /\ ((Znth k_3 weights_l 0) <= (capacity_pre + 1 ))))) (PreH8 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((0 <= (Znth k_4 values_l 0)) /\ ((Znth k_4 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((capacity_pre + 1 ) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= (capacity_pre + 1 )) ” 
  &&  “ ((capacity_pre + 1 ) <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((1 <= (Znth k weights_l 0)) /\ ((Znth k weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 values_l 0)) /\ ((Znth k_2 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_entail_wit_2 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 weights_l 0)) /\ ((Znth k_4 weights_l 0) <= (capacity_pre + 1 ))))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 values_l 0)) /\ ((Znth k_5 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (0 * width )) ” 
  &&  “ ((0 * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (0 * width ) dp_l )
  **  (IntArray.undef_seg dp_pre (0 * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n_pre)) -> ((1 <= (Znth k_4 weights_l 0)) /\ ((Znth k_4 weights_l 0) <= (capacity_pre + 1 ))))) (PreH11 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((0 <= (Znth k_5 values_l 0)) /\ ((Znth k_5 values_l 0) <= 10000)))) ,
  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (0 * width )) ” 
  &&  “ ((0 * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.seg dp_pre 0 (0 * width ) dp_l )
  **  (IntArray.undef_seg dp_pre (0 * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
).

Definition zeroOneKnapsack_entail_wit_3 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (i * width ))) (PreH14 : ((i * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 i )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH17 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH18 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (i * width ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= ((i * width ) + 0 )) ” 
  &&  “ (((i * width ) + 0 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + 0 ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + 0 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (i * width ))) (PreH14 : ((i * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 i )) (PreH16 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH17 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH18 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i * width ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= ((i * width ) + 0 )) ” 
  &&  “ (((i * width ) + 0 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.seg dp_pre 0 ((i * width ) + 0 ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_4 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH20 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (((i * width ) + j ) = ((i * width ) + j )) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((((i * width ) + j ) + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH20 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((((i * width ) + j ) + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_4_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH20 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))
.

Definition zeroOneKnapsack_entail_wit_4_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH20 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((((i * width ) + j ) + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))
.

Definition zeroOneKnapsack_entail_wit_4_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH20 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))
.

Definition zeroOneKnapsack_entail_wit_5 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (i = 0)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (idx = ((i * width ) + j ))) (PreH16 : (0 <= idx)) (PreH17 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : (0 <= idx)) (PreH20 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH22 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH23 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH24 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (idx + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j 0 ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (i = 0)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (idx = ((i * width ) + j ))) (PreH16 : (0 <= idx)) (PreH17 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : (0 <= idx)) (PreH20 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH22 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH23 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH24 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (((0 <= (Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) <= 4000000))) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons (0) ((@nil Z))))) i (j + 1 ) ) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j 0 ) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_5_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (i = 0)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (idx = ((i * width ) + j ))) (PreH16 : (0 <= idx)) (PreH17 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : (0 <= idx)) (PreH20 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH22 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH23 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH24 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (((0 <= (Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) <= 4000000)))
.

Definition zeroOneKnapsack_entail_wit_5_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (i = 0)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (idx = ((i * width ) + j ))) (PreH16 : (0 <= idx)) (PreH17 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : (0 <= idx)) (PreH20 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH22 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH23 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH24 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons (0) ((@nil Z))))) i (j + 1 ) )
.

Definition zeroOneKnapsack_entail_wit_5_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (i = 0)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (idx = ((i * width ) + j ))) (PreH16 : (0 <= idx)) (PreH17 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : (0 <= idx)) (PreH20 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH22 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH23 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH24 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackCellCorrect weights_l values_l i j 0 )
.

Definition zeroOneKnapsack_entail_wit_6 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (idx + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (j = 0) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j 0 ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (((0 <= (Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) <= 4000000))) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons (0) ((@nil Z))))) i (j + 1 ) ) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j 0 ) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_6_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (((0 <= (Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons (0) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) 0) <= 4000000)))
.

Definition zeroOneKnapsack_entail_wit_6_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons (0) ((@nil Z))))) i (j + 1 ) )
.

Definition zeroOneKnapsack_entail_wit_6_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackCellCorrect weights_l values_l i j 0 )
.

Definition zeroOneKnapsack_entail_wit_7 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg dp_pre 0 idx dp_l_2 )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ ((i - 1 ) = (i - 1 )) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) = (Znth (i - 1 ) weights_l 0)) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) = (Znth (i - 1 ) values_l 0)) ” 
  &&  “ (1 <= (Znth (i - 1 ) weights_l 0)) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= (Znth (i - 1 ) values_l 0)) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < idx) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < idx) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= 10000) ” 
  &&  “ (0 <= (Znth (i - 1 ) values_l 0)) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= (capacity_pre + 1 )) ” 
  &&  “ (1 <= (Znth (i - 1 ) weights_l 0)) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_7_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))
.

Definition zeroOneKnapsack_entail_wit_7_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((((i - 1 ) * width ) + j ) < idx)
.

Definition zeroOneKnapsack_entail_wit_7_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((Znth (i - 1 ) values_l 0) <= 10000)
.

Definition zeroOneKnapsack_entail_wit_7_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (0 <= (Znth (i - 1 ) values_l 0))
.

Definition zeroOneKnapsack_entail_wit_7_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((Znth (i - 1 ) weights_l 0) <= (capacity_pre + 1 ))
.

Definition zeroOneKnapsack_entail_wit_7_split_goal_6 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH23 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH24 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (1 <= (Znth (i - 1 ) weights_l 0))
.

Definition zeroOneKnapsack_entail_wit_8 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH32 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l_2: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (0 <= item) ” 
  &&  “ (item < n_pre) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0)) ” 
  &&  “ (0 <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= 4000000) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) j (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l_2)))) -> ((0 <= (Znth k dp_l_2 0)) /\ ((Znth k dp_l_2 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l_2 )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH32 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) j (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) ) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= 4000000) ” 
  &&  “ (0 <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) = (Znth (((i - 1 ) * width ) + j ) dp_l 0)) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_8_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH32 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackCellCorrect weights_l values_l (i - 1 ) j (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) )
.

Definition zeroOneKnapsack_entail_wit_8_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH32 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= 4000000)
.

Definition zeroOneKnapsack_entail_wit_8_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH32 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (0 <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
.

Definition zeroOneKnapsack_entail_wit_8_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH32 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) = (Znth (((i - 1 ) * width ) + j ) dp_l 0))
.

Definition zeroOneKnapsack_entail_wit_9 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w <= j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l_2 )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (0 <= item) ” 
  &&  “ (item < n_pre) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= j) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0)) ” 
  &&  “ (0 <= without) ” 
  &&  “ (without <= 4000000) ” 
  &&  “ (0 <= (j - w )) ” 
  &&  “ ((j - w ) <= capacity_pre) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + (j - w ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - w ) ) < idx) ” 
  &&  “ ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) j without ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w <= j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - w ) ) < idx) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_9_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w <= j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))
.

Definition zeroOneKnapsack_entail_wit_9_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w <= j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((((i - 1 ) * width ) + (j - w ) ) < idx)
.

Definition zeroOneKnapsack_entail_wit_10 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l_2: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (0 <= item) ” 
  &&  “ (item < n_pre) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= j) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0)) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0)) ” 
  &&  “ (0 <= without) ” 
  &&  “ (without <= 4000000) ” 
  &&  “ (0 <= (Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0)) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) <= 4000000) ” 
  &&  “ (INT_MIN <= ((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) + v )) ” 
  &&  “ (((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) + v ) <= INT_MAX) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) j without ) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) (Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l_2)))) -> ((0 <= (Znth k dp_l_2 0)) /\ ((Znth k dp_l_2 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l_2 )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) (Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) ) ” 
  &&  “ (((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) + v ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) + v )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) <= 4000000) ” 
  &&  “ (0 <= (Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0)) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l 0)) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_10_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) (Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) )
.

Definition zeroOneKnapsack_entail_wit_10_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) + v ) <= INT_MAX)
.

Definition zeroOneKnapsack_entail_wit_10_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (INT_MIN <= ((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) + v ))
.

Definition zeroOneKnapsack_entail_wit_10_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) <= 4000000)
.

Definition zeroOneKnapsack_entail_wit_10_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (0 <= (Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0))
.

Definition zeroOneKnapsack_entail_wit_10_split_goal_6 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l)))) -> ((0 <= (Znth k_4 dp_l 0)) /\ ((Znth k_4 dp_l 0) <= 4000000)))) (PreH38 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0) = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l 0))
.

Definition zeroOneKnapsack_entail_wit_11 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) > without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (idx + 1 ) (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= j) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0)) ” 
  &&  “ (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l 0)) ” 
  &&  “ ((prev + v ) = (prev + v )) ” 
  &&  “ ((prev + v ) > without) ” 
  &&  “ (0 <= (prev + v )) ” 
  &&  “ ((prev + v ) <= 4000000) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j (prev + v ) ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) > without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (((0 <= (Znth 0 (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0) <= 4000000))) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) i (j + 1 ) ) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j (prev + v ) ) ” 
  &&  “ ((prev + v ) <= 4000000) ” 
  &&  “ (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0)) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0)) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_11_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) > without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (((0 <= (Znth 0 (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0) <= 4000000)))
.

Definition zeroOneKnapsack_entail_wit_11_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) > without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) i (j + 1 ) )
.

Definition zeroOneKnapsack_entail_wit_11_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) > without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackCellCorrect weights_l values_l i j (prev + v ) )
.

Definition zeroOneKnapsack_entail_wit_11_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) > without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  ((prev + v ) <= 4000000)
.

Definition zeroOneKnapsack_entail_wit_11_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) > without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0))
.

Definition zeroOneKnapsack_entail_wit_11_split_goal_6 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) > without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (without = (Znth (((i - 1 ) * width ) + j ) (app (dp_l_2) ((cons ((prev + v )) ((@nil Z))))) 0))
.

Definition zeroOneKnapsack_entail_wit_12 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) <= without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (idx + 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= j) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0)) ” 
  &&  “ (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l 0)) ” 
  &&  “ ((prev + v ) = (prev + v )) ” 
  &&  “ ((prev + v ) <= without) ” 
  &&  “ (0 <= without) ” 
  &&  “ (without <= 4000000) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j without ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) <= without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (((0 <= (Znth 0 (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons (without) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons (without) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons (without) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0) <= 4000000))) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons (without) ((@nil Z))))) i (j + 1 ) ) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j without ) ” 
  &&  “ (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_12_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) <= without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (((0 <= (Znth 0 (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons (without) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons (without) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons (without) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0) <= 4000000)))
.

Definition zeroOneKnapsack_entail_wit_12_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) <= without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons (without) ((@nil Z))))) i (j + 1 ) )
.

Definition zeroOneKnapsack_entail_wit_12_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) <= without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackCellCorrect weights_l values_l i j without )
.

Definition zeroOneKnapsack_entail_wit_12_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) <= without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0))
.

Definition zeroOneKnapsack_entail_wit_12_split_goal_5 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) <= without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH39 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH40 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (without = (Znth (((i - 1 ) * width ) + j ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0))
.

Definition zeroOneKnapsack_entail_wit_13 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w > j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (idx + 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (j < w) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0)) ” 
  &&  “ (0 <= without) ” 
  &&  “ (without <= 4000000) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j without ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w > j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (((0 <= (Znth 0 (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons (without) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons (without) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons (without) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0) <= 4000000))) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons (without) ((@nil Z))))) i (j + 1 ) ) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l i j without ) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_13_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w > j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (((0 <= (Znth 0 (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) /\ ((Znth 0 (app (dp_l_2) ((cons (without) ((@nil Z))))) 0) <= 4000000)) /\ ((0 <= (Znth ((Zlength ((app (dp_l_2) ((cons (without) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0)) /\ ((Znth ((Zlength ((app (dp_l_2) ((cons (without) ((@nil Z))))))) - 1 ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0) <= 4000000)))
.

Definition zeroOneKnapsack_entail_wit_13_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w > j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackRowProgress weights_l values_l capacity_pre (app (dp_l_2) ((cons (without) ((@nil Z))))) i (j + 1 ) )
.

Definition zeroOneKnapsack_entail_wit_13_split_goal_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w > j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (KnapsackCellCorrect weights_l values_l i j without )
.

Definition zeroOneKnapsack_entail_wit_13_split_goal_4 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w > j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (without = (Znth (((i - 1 ) * width ) + j ) (app (dp_l_2) ((cons (without) ((@nil Z))))) 0))
.

Definition zeroOneKnapsack_entail_wit_14_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (w = (Znth item weights_l 0))) (PreH16 : (v = (Znth item values_l 0))) (PreH17 : (j < w)) (PreH18 : (idx = ((i * width ) + j ))) (PreH19 : (0 <= idx)) (PreH20 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH23 : (0 <= without)) (PreH24 : (without <= 4000000)) (PreH25 : (KnapsackCellCorrect weights_l values_l i j without )) (PreH26 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i (j + 1 ) )) (PreH27 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH28 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH29 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_entail_wit_14_2 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (with_val: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (w = (Znth item weights_l 0))) (PreH16 : (v = (Znth item values_l 0))) (PreH17 : (1 <= w)) (PreH18 : (w <= j)) (PreH19 : (0 <= v)) (PreH20 : (v <= 10000)) (PreH21 : (idx = ((i * width ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH24 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH25 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH26 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH27 : (with_val = (prev + v ))) (PreH28 : (with_val <= without)) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l i j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i (j + 1 ) )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_entail_wit_14_3 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (with_val: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (w = (Znth item weights_l 0))) (PreH16 : (v = (Znth item values_l 0))) (PreH17 : (1 <= w)) (PreH18 : (w <= j)) (PreH19 : (0 <= v)) (PreH20 : (v <= 10000)) (PreH21 : (idx = ((i * width ) + j ))) (PreH22 : (0 <= idx)) (PreH23 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH24 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH25 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l_2 0))) (PreH26 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l_2 0))) (PreH27 : (with_val = (prev + v ))) (PreH28 : (with_val > without)) (PreH29 : (0 <= with_val)) (PreH30 : (with_val <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l i j with_val )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i (j + 1 ) )) (PreH33 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH34 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_entail_wit_14_4 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (j = 0)) (PreH13 : (idx = ((i * width ) + j ))) (PreH14 : (0 <= idx)) (PreH15 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH16 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackCellCorrect weights_l values_l i j 0 )) (PreH18 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i (j + 1 ) )) (PreH19 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH20 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH21 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_entail_wit_14_5 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (idx = ((i * width ) + j ))) (PreH15 : (0 <= idx)) (PreH16 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (KnapsackCellCorrect weights_l values_l i j 0 )) (PreH19 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i (j + 1 ) )) (PreH20 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH21 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH22 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_entail_wit_15 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (idx = ((i * width ) + j ))) (PreH15 : (0 <= idx)) (PreH16 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i (j + 1 ) )) (PreH19 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH20 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH21 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= ((i * width ) + (j + 1 ) )) ” 
  &&  “ (((i * width ) + (j + 1 ) ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (0 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (idx = ((i * width ) + j ))) (PreH15 : (0 <= idx)) (PreH16 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i (j + 1 ) )) (PreH19 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH20 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH21 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (idx + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= ((i * width ) + (j + 1 ) )) ” 
  &&  “ (((i * width ) + (j + 1 ) ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_16 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH20 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l (i + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i + 1 ) * width ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i + 1 ) * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= (capacity_pre + 1 ))) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) (PreH18 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH19 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH20 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l (i + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.seg dp_pre 0 ((i + 1 ) * width ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i + 1 ) * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
).

Definition zeroOneKnapsack_entail_wit_17 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 (i + 1 ) )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH14 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH15 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i + 1 ) * width ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre ((i + 1 ) * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (0 <= ((i + 1 ) * width )) ” 
  &&  “ (((i + 1 ) * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l (i + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i + 1 ) * width ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i + 1 ) * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 (i + 1 ) )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH14 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH15 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (((i + 1 ) * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_17_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (i: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 (i + 1 ) )) (PreH13 : forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < (Zlength (dp_l_2)))) -> ((0 <= (Znth k_4 dp_l_2 0)) /\ ((Znth k_4 dp_l_2 0) <= 4000000)))) (PreH14 : forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < n_pre)) -> ((1 <= (Znth k_5 weights_l 0)) /\ ((Znth k_5 weights_l 0) <= (capacity_pre + 1 ))))) (PreH15 : forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < n_pre)) -> ((0 <= (Znth k_6 values_l 0)) /\ ((Znth k_6 values_l 0) <= 10000)))) ,
  (((i + 1 ) * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))
.

Definition zeroOneKnapsack_entail_wit_18 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i > n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (i * width ))) (PreH14 : ((i * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 i )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l_2)))) -> ((0 <= (Znth k dp_l_2 0)) /\ ((Znth k dp_l_2 0) <= 4000000)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH18 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (i * width ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= ((n_pre * width ) + capacity_pre )) ” 
  &&  “ (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l (n_pre + 1 ) ) ” 
  &&  “ (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ” 
  &&  “ (0 <= (Znth ((n_pre * width ) + capacity_pre ) dp_l 0)) ” 
  &&  “ ((Znth ((n_pre * width ) + capacity_pre ) dp_l 0) <= 4000000) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i > n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= (n_pre + 1 ))) (PreH13 : (0 <= (i * width ))) (PreH14 : ((i * width ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 i )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l_2)))) -> ((0 <= (Znth k dp_l_2 0)) /\ ((Znth k dp_l_2 0) <= 4000000)))) (PreH17 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH18 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.seg dp_pre 0 (i * width ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= ((n_pre * width ) + capacity_pre )) ” 
  &&  “ (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l (n_pre + 1 ) ) ” 
  &&  “ (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ” 
  &&  “ (0 <= (Znth ((n_pre * width ) + capacity_pre ) dp_l 0)) ” 
  &&  “ ((Znth ((n_pre * width ) + capacity_pre ) dp_l 0) <= 4000000) ”
  &&  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_return_wit_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH11 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH12 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 (n_pre + 1 ) )) (PreH13 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l_2 0) )) (PreH14 : (0 <= (Znth ((n_pre * width ) + capacity_pre ) dp_l_2 0))) (PreH15 : ((Znth ((n_pre * width ) + capacity_pre ) dp_l_2 0) <= 4000000)) ,
  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l_2 0) ) ” 
  &&  “ (0 <= (Znth ((n_pre * width ) + capacity_pre ) dp_l_2 0)) ” 
  &&  “ ((Znth ((n_pre * width ) + capacity_pre ) dp_l_2 0) <= 4000000) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l (n_pre + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
.

Definition zeroOneKnapsack_partial_solve_wit_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (i = 0)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (0 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (0 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (idx = ((i * width ) + j ))) (PreH16 : (0 <= idx)) (PreH17 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : (0 <= idx)) (PreH20 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH22 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH23 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH24 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (i = 0) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (((dp_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
.

Definition zeroOneKnapsack_partial_solve_wit_2 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH24 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (j = 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (((dp_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
.

Definition zeroOneKnapsack_partial_solve_wit_3 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH24 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (((weights_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.missing_i weights_pre (i - 1 ) 0 n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_partial_solve_wit_4 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (idx: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (0 <= n_pre)) (PreH5 : (n_pre <= 300)) (PreH6 : (0 <= capacity_pre)) (PreH7 : (capacity_pre <= 300)) (PreH8 : (1 <= width)) (PreH9 : (width <= 301)) (PreH10 : ((Zlength (weights_l)) = n_pre)) (PreH11 : ((Zlength (values_l)) = n_pre)) (PreH12 : (0 <= i)) (PreH13 : (i <= n_pre)) (PreH14 : (0 <= j)) (PreH15 : (j <= capacity_pre)) (PreH16 : (idx = ((i * width ) + j ))) (PreH17 : (0 <= idx)) (PreH18 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH19 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (0 <= idx)) (PreH21 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH23 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH24 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH25 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (((values_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.missing_i values_pre (i - 1 ) 0 n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_partial_solve_wit_5 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= (capacity_pre + 1 ))) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (0 <= (((i - 1 ) * width ) + j ))) (PreH28 : ((((i - 1 ) * width ) + j ) < idx)) (PreH29 : ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH31 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH32 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH33 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (0 <= item) ” 
  &&  “ (item < n_pre) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < idx) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (((dp_pre + ((((i - 1 ) * width ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.missing_i dp_pre (((i - 1 ) * width ) + j ) 0 idx dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_partial_solve_wit_6 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (1 <= j)) (PreH13 : (j <= capacity_pre)) (PreH14 : (item = (i - 1 ))) (PreH15 : (0 <= item)) (PreH16 : (item < n_pre)) (PreH17 : (w = (Znth item weights_l 0))) (PreH18 : (v = (Znth item values_l 0))) (PreH19 : (1 <= w)) (PreH20 : (w <= j)) (PreH21 : (0 <= v)) (PreH22 : (v <= 10000)) (PreH23 : (idx = ((i * width ) + j ))) (PreH24 : (0 <= idx)) (PreH25 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH26 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH28 : (0 <= without)) (PreH29 : (without <= 4000000)) (PreH30 : (0 <= (j - w ))) (PreH31 : ((j - w ) <= capacity_pre)) (PreH32 : (0 <= (((i - 1 ) * width ) + (j - w ) ))) (PreH33 : ((((i - 1 ) * width ) + (j - w ) ) < idx)) (PreH34 : ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH35 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH36 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH37 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH38 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH39 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (0 <= item) ” 
  &&  “ (item < n_pre) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= j) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0)) ” 
  &&  “ (0 <= without) ” 
  &&  “ (without <= 4000000) ” 
  &&  “ (0 <= (j - w )) ” 
  &&  “ ((j - w ) <= capacity_pre) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + (j - w ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - w ) ) < idx) ” 
  &&  “ ((((i - 1 ) * width ) + (j - w ) ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) j without ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (((dp_pre + ((((i - 1 ) * width ) + (j - w ) ) * sizeof(INT)))) # Int  |-> (Znth ((((i - 1 ) * width ) + (j - w ) ) - 0 ) dp_l 0))
  **  (IntArray.missing_i dp_pre (((i - 1 ) * width ) + (j - w ) ) 0 idx dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_partial_solve_wit_7 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) > without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH40 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((prev + v ) > without) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (0 <= item) ” 
  &&  “ (item < n_pre) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= j) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0)) ” 
  &&  “ (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l 0)) ” 
  &&  “ (0 <= without) ” 
  &&  “ (without <= 4000000) ” 
  &&  “ (0 <= prev) ” 
  &&  “ (prev <= 4000000) ” 
  &&  “ (INT_MIN <= (prev + v )) ” 
  &&  “ ((prev + v ) <= INT_MAX) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) j without ) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (((dp_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
.

Definition zeroOneKnapsack_partial_solve_wit_8 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (prev: Z) (PreH1 : ((prev + v ) <= without)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= j)) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH29 : (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l 0))) (PreH30 : (0 <= without)) (PreH31 : (without <= 4000000)) (PreH32 : (0 <= prev)) (PreH33 : (prev <= 4000000)) (PreH34 : (INT_MIN <= (prev + v ))) (PreH35 : ((prev + v ) <= INT_MAX)) (PreH36 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH37 : (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH39 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH40 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH41 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((prev + v ) <= without) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (0 <= item) ” 
  &&  “ (item < n_pre) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= j) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0)) ” 
  &&  “ (prev = (Znth (((i - 1 ) * width ) + (j - w ) ) dp_l 0)) ” 
  &&  “ (0 <= without) ” 
  &&  “ (without <= 4000000) ” 
  &&  “ (0 <= prev) ” 
  &&  “ (prev <= 4000000) ” 
  &&  “ (INT_MIN <= (prev + v )) ” 
  &&  “ ((prev + v ) <= INT_MAX) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) j without ) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) (j - w ) prev ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (((dp_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
.

Definition zeroOneKnapsack_partial_solve_wit_9 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (i: Z) (j: Z) (item: Z) (w: Z) (v: Z) (idx: Z) (without: Z) (PreH1 : (w > j)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (1 <= width)) (PreH8 : (width <= 301)) (PreH9 : ((Zlength (weights_l)) = n_pre)) (PreH10 : ((Zlength (values_l)) = n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= n_pre)) (PreH13 : (1 <= j)) (PreH14 : (j <= capacity_pre)) (PreH15 : (item = (i - 1 ))) (PreH16 : (0 <= item)) (PreH17 : (item < n_pre)) (PreH18 : (w = (Znth item weights_l 0))) (PreH19 : (v = (Znth item values_l 0))) (PreH20 : (1 <= w)) (PreH21 : (w <= (capacity_pre + 1 ))) (PreH22 : (0 <= v)) (PreH23 : (v <= 10000)) (PreH24 : (idx = ((i * width ) + j ))) (PreH25 : (0 <= idx)) (PreH26 : (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH27 : ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH28 : (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0))) (PreH29 : (0 <= without)) (PreH30 : (without <= 4000000)) (PreH31 : (KnapsackCellCorrect weights_l values_l (i - 1 ) j without )) (PreH32 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) (PreH33 : forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000)))) (PreH34 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 ))))) (PreH35 : forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000)))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
  **  (IntArray.undef_seg dp_pre idx ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (w > j) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (item = (i - 1 )) ” 
  &&  “ (0 <= item) ” 
  &&  “ (item < n_pre) ” 
  &&  “ (w = (Znth item weights_l 0)) ” 
  &&  “ (v = (Znth item values_l 0)) ” 
  &&  “ (1 <= w) ” 
  &&  “ (w <= (capacity_pre + 1 )) ” 
  &&  “ (0 <= v) ” 
  &&  “ (v <= 10000) ” 
  &&  “ (idx = ((i * width ) + j )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ ((idx + 1 ) <= ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (without = (Znth (((i - 1 ) * width ) + j ) dp_l 0)) ” 
  &&  “ (0 <= without) ” 
  &&  “ (without <= 4000000) ” 
  &&  “ (KnapsackCellCorrect weights_l values_l (i - 1 ) j without ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (Zlength (dp_l)))) -> ((0 <= (Znth k dp_l 0)) /\ ((Znth k dp_l 0) <= 4000000))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((1 <= (Znth k_2 weights_l 0)) /\ ((Znth k_2 weights_l 0) <= (capacity_pre + 1 )))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((0 <= (Znth k_3 values_l 0)) /\ ((Znth k_3 values_l 0) <= 10000))) ”
  &&  (((dp_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (idx + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 idx dp_l )
.

Definition zeroOneKnapsack_partial_solve_wit_10 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (1 <= width)) (PreH7 : (width <= 301)) (PreH8 : ((Zlength (weights_l)) = n_pre)) (PreH9 : ((Zlength (values_l)) = n_pre)) (PreH10 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH11 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH12 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l (n_pre + 1 ) )) (PreH13 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) (PreH14 : (0 <= (Znth ((n_pre * width ) + capacity_pre ) dp_l 0))) (PreH15 : ((Znth ((n_pre * width ) + capacity_pre ) dp_l 0) <= 4000000)) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (1 <= width) ” 
  &&  “ (width <= 301) ” 
  &&  “ ((Zlength (weights_l)) = n_pre) ” 
  &&  “ ((Zlength (values_l)) = n_pre) ” 
  &&  “ (0 <= ((n_pre * width ) + capacity_pre )) ” 
  &&  “ (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l (n_pre + 1 ) ) ” 
  &&  “ (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ” 
  &&  “ (0 <= (Znth ((n_pre * width ) + capacity_pre ) dp_l 0)) ” 
  &&  “ ((Znth ((n_pre * width ) + capacity_pre ) dp_l 0) <= 4000000) ”
  &&  (((dp_pre + (((n_pre * width ) + capacity_pre ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre * width ) + capacity_pre ) dp_l 0))
  **  (IntArray.missing_i dp_pre ((n_pre * width ) + capacity_pre ) 0 ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_zeroOneKnapsack_safety_wit_1 : zeroOneKnapsack_safety_wit_1.
Axiom proof_of_zeroOneKnapsack_safety_wit_2 : zeroOneKnapsack_safety_wit_2.
Axiom proof_of_zeroOneKnapsack_safety_wit_3 : zeroOneKnapsack_safety_wit_3.
Axiom proof_of_zeroOneKnapsack_safety_wit_4 : zeroOneKnapsack_safety_wit_4.
Axiom proof_of_zeroOneKnapsack_safety_wit_5 : zeroOneKnapsack_safety_wit_5.
Axiom proof_of_zeroOneKnapsack_safety_wit_6 : zeroOneKnapsack_safety_wit_6.
Axiom proof_of_zeroOneKnapsack_safety_wit_7 : zeroOneKnapsack_safety_wit_7.
Axiom proof_of_zeroOneKnapsack_safety_wit_8 : zeroOneKnapsack_safety_wit_8.
Axiom proof_of_zeroOneKnapsack_safety_wit_9 : zeroOneKnapsack_safety_wit_9.
Axiom proof_of_zeroOneKnapsack_safety_wit_10 : zeroOneKnapsack_safety_wit_10.
Axiom proof_of_zeroOneKnapsack_safety_wit_11 : zeroOneKnapsack_safety_wit_11.
Axiom proof_of_zeroOneKnapsack_safety_wit_12 : zeroOneKnapsack_safety_wit_12.
Axiom proof_of_zeroOneKnapsack_safety_wit_13 : zeroOneKnapsack_safety_wit_13.
Axiom proof_of_zeroOneKnapsack_safety_wit_14 : zeroOneKnapsack_safety_wit_14.
Axiom proof_of_zeroOneKnapsack_safety_wit_15 : zeroOneKnapsack_safety_wit_15.
Axiom proof_of_zeroOneKnapsack_safety_wit_16 : zeroOneKnapsack_safety_wit_16.
Axiom proof_of_zeroOneKnapsack_safety_wit_17 : zeroOneKnapsack_safety_wit_17.
Axiom proof_of_zeroOneKnapsack_safety_wit_18 : zeroOneKnapsack_safety_wit_18.
Axiom proof_of_zeroOneKnapsack_safety_wit_19 : zeroOneKnapsack_safety_wit_19.
Axiom proof_of_zeroOneKnapsack_safety_wit_20 : zeroOneKnapsack_safety_wit_20.
Axiom proof_of_zeroOneKnapsack_safety_wit_21 : zeroOneKnapsack_safety_wit_21.
Axiom proof_of_zeroOneKnapsack_safety_wit_22 : zeroOneKnapsack_safety_wit_22.
Axiom proof_of_zeroOneKnapsack_safety_wit_23 : zeroOneKnapsack_safety_wit_23.
Axiom proof_of_zeroOneKnapsack_safety_wit_24 : zeroOneKnapsack_safety_wit_24.
Axiom proof_of_zeroOneKnapsack_safety_wit_25 : zeroOneKnapsack_safety_wit_25.
Axiom proof_of_zeroOneKnapsack_safety_wit_26 : zeroOneKnapsack_safety_wit_26.
Axiom proof_of_zeroOneKnapsack_entail_wit_1 : zeroOneKnapsack_entail_wit_1.
Axiom proof_of_zeroOneKnapsack_entail_wit_2 : zeroOneKnapsack_entail_wit_2.
Axiom proof_of_zeroOneKnapsack_entail_wit_3 : zeroOneKnapsack_entail_wit_3.
Axiom proof_of_zeroOneKnapsack_entail_wit_4 : zeroOneKnapsack_entail_wit_4.
Axiom proof_of_zeroOneKnapsack_entail_wit_5 : zeroOneKnapsack_entail_wit_5.
Axiom proof_of_zeroOneKnapsack_entail_wit_6 : zeroOneKnapsack_entail_wit_6.
Axiom proof_of_zeroOneKnapsack_entail_wit_7 : zeroOneKnapsack_entail_wit_7.
Axiom proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8.
Axiom proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9.
Axiom proof_of_zeroOneKnapsack_entail_wit_10 : zeroOneKnapsack_entail_wit_10.
Axiom proof_of_zeroOneKnapsack_entail_wit_11 : zeroOneKnapsack_entail_wit_11.
Axiom proof_of_zeroOneKnapsack_entail_wit_12 : zeroOneKnapsack_entail_wit_12.
Axiom proof_of_zeroOneKnapsack_entail_wit_13 : zeroOneKnapsack_entail_wit_13.
Axiom proof_of_zeroOneKnapsack_entail_wit_14_1 : zeroOneKnapsack_entail_wit_14_1.
Axiom proof_of_zeroOneKnapsack_entail_wit_14_2 : zeroOneKnapsack_entail_wit_14_2.
Axiom proof_of_zeroOneKnapsack_entail_wit_14_3 : zeroOneKnapsack_entail_wit_14_3.
Axiom proof_of_zeroOneKnapsack_entail_wit_14_4 : zeroOneKnapsack_entail_wit_14_4.
Axiom proof_of_zeroOneKnapsack_entail_wit_14_5 : zeroOneKnapsack_entail_wit_14_5.
Axiom proof_of_zeroOneKnapsack_entail_wit_15 : zeroOneKnapsack_entail_wit_15.
Axiom proof_of_zeroOneKnapsack_entail_wit_16 : zeroOneKnapsack_entail_wit_16.
Axiom proof_of_zeroOneKnapsack_entail_wit_17 : zeroOneKnapsack_entail_wit_17.
Axiom proof_of_zeroOneKnapsack_entail_wit_18 : zeroOneKnapsack_entail_wit_18.
Axiom proof_of_zeroOneKnapsack_return_wit_1 : zeroOneKnapsack_return_wit_1.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_1 : zeroOneKnapsack_partial_solve_wit_1.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_2 : zeroOneKnapsack_partial_solve_wit_2.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_3 : zeroOneKnapsack_partial_solve_wit_3.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_4 : zeroOneKnapsack_partial_solve_wit_4.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_5 : zeroOneKnapsack_partial_solve_wit_5.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_6 : zeroOneKnapsack_partial_solve_wit_6.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_7 : zeroOneKnapsack_partial_solve_wit_7.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_8 : zeroOneKnapsack_partial_solve_wit_8.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_9 : zeroOneKnapsack_partial_solve_wit_9.
Axiom proof_of_zeroOneKnapsack_partial_solve_wit_10 : zeroOneKnapsack_partial_solve_wit_10.

End VC_Correct.
