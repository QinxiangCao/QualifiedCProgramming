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
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre )) ,
  ((( &( "width" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((capacity_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (capacity_pre + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_2 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre )) ,
  ((( &( "width" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_3 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "width" ) )) # Int  |-> (capacity_pre + 1 ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_4 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (width: Z) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l i )) ,
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
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
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
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
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
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= ((i * width ) + j ))) (PreH2 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (width <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (width >= INT_MIN)) (PreH11 : (capacity_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (j <= capacity_pre)) (PreH14 : (width = (capacity_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 300)) (PreH17 : (0 <= capacity_pre)) (PreH18 : (capacity_pre <= 300)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= (capacity_pre + 1 ))) (PreH23 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_8 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_9 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i <> 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_10 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_11 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "item" ) )) # Int  |->_)
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_12 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "item" ) )) # Int  |->_)
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_13 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : ((i - 1 ) <= INT_MAX)) (PreH4 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH6 : ((i - 1 ) >= INT_MIN)) (PreH7 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH9 : (0 <= (i - 1 ))) (PreH10 : ((i - 1 ) < n_pre)) (PreH11 : (((i * width ) + j ) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : (j <> 0)) (PreH14 : (i <> 0)) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : (0 <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : (0 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (0 <= j)) (PreH36 : (j <= (capacity_pre + 1 ))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "without" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((((i - 1 ) * width ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - 1 ) * width ) + j )) ”
.

Definition zeroOneKnapsack_safety_wit_14 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : ((i - 1 ) <= INT_MAX)) (PreH4 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH6 : ((i - 1 ) >= INT_MIN)) (PreH7 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH9 : (0 <= (i - 1 ))) (PreH10 : ((i - 1 ) < n_pre)) (PreH11 : (((i * width ) + j ) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : (j <> 0)) (PreH14 : (i <> 0)) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : (0 <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : (0 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (0 <= j)) (PreH36 : (j <= (capacity_pre + 1 ))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "without" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((i - 1 ) * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - 1 ) * width )) ”
.

Definition zeroOneKnapsack_safety_wit_15 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : ((i - 1 ) <= INT_MAX)) (PreH4 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH6 : ((i - 1 ) >= INT_MIN)) (PreH7 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH9 : (0 <= (i - 1 ))) (PreH10 : ((i - 1 ) < n_pre)) (PreH11 : (((i * width ) + j ) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : (j <> 0)) (PreH14 : (i <> 0)) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : (0 <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : (0 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (0 <= j)) (PreH36 : (j <= (capacity_pre + 1 ))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "without" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_16 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : ((i - 1 ) <= INT_MAX)) (PreH4 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH6 : ((i - 1 ) >= INT_MIN)) (PreH7 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH9 : (0 <= (i - 1 ))) (PreH10 : ((i - 1 ) < n_pre)) (PreH11 : (((i * width ) + j ) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : (j <> 0)) (PreH14 : (i <> 0)) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : (0 <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : (0 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (0 <= j)) (PreH36 : (j <= (capacity_pre + 1 ))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "without" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_17 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ”
.

Definition zeroOneKnapsack_safety_wit_18 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((j - (Znth (i - 1 ) weights_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - (Znth (i - 1 ) weights_l 0) )) ”
.

Definition zeroOneKnapsack_safety_wit_19 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((i - 1 ) * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - 1 ) * width )) ”
.

Definition zeroOneKnapsack_safety_wit_20 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_21 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_22 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "with_val" ) )) # Int  |->_)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "prev" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) )) ”
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "with_val" ) )) # Int  |->_)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "prev" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) )) ”
).

Definition zeroOneKnapsack_safety_wit_22_split_goal_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "with_val" ) )) # Int  |->_)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "prev" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= INT_MAX) ”
.

Definition zeroOneKnapsack_safety_wit_22_split_goal_2 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "with_val" ) )) # Int  |->_)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "prev" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((INT_MIN) <= ((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) )) ”
.

Definition zeroOneKnapsack_safety_wit_23 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
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
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_24 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
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
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_25 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : ((i - 1 ) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (((i * width ) + j ) <= INT_MAX)) (PreH18 : (((i * width ) + j ) >= INT_MIN)) (PreH19 : (j <> 0)) (PreH20 : (i <> 0)) (PreH21 : (0 <= ((i * width ) + j ))) (PreH22 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1 ))) (PreH35 : (0 <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : (0 <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : (0 <= i)) (PreH40 : (i <= n_pre)) (PreH41 : (0 <= j)) (PreH42 : (j <= (capacity_pre + 1 ))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_26 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : ((i - 1 ) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (((i * width ) + j ) <= INT_MAX)) (PreH18 : (((i * width ) + j ) >= INT_MIN)) (PreH19 : (j <> 0)) (PreH20 : (i <> 0)) (PreH21 : (0 <= ((i * width ) + j ))) (PreH22 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1 ))) (PreH35 : (0 <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : (0 <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : (0 <= i)) (PreH40 : (i <= n_pre)) (PreH41 : (0 <= j)) (PreH42 : (j <= (capacity_pre + 1 ))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_27 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) > j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : ((i - 1 ) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (((i * width ) + j ) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : (j <> 0)) (PreH15 : (i <> 0)) (PreH16 : (0 <= ((i * width ) + j ))) (PreH17 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1 ))) (PreH30 : (0 <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : (0 <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : (0 <= i)) (PreH35 : (i <= n_pre)) (PreH36 : (0 <= j)) (PreH37 : (j <= (capacity_pre + 1 ))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_28 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_29 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ (((n_pre * width ) + capacity_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre * width ) + capacity_pre )) ”
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ (((n_pre * width ) + capacity_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre * width ) + capacity_pre )) ”
).

Definition zeroOneKnapsack_safety_wit_29_split_goal_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ (((n_pre * width ) + capacity_pre ) <= INT_MAX) ”
.

Definition zeroOneKnapsack_safety_wit_29_split_goal_2 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ ((INT_MIN) <= ((n_pre * width ) + capacity_pre )) ”
.

Definition zeroOneKnapsack_safety_wit_30 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ ((n_pre * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * width )) ”
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ ((n_pre * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * width )) ”
).

Definition zeroOneKnapsack_safety_wit_30_split_goal_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ ((n_pre * width ) <= INT_MAX) ”
.

Definition zeroOneKnapsack_safety_wit_30_split_goal_2 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ ((INT_MIN) <= (n_pre * width )) ”
.

Definition zeroOneKnapsack_entail_wit_1 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ ((capacity_pre + 1 ) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre (capacity_pre + 1 ) dp_l 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (0 * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg dp_pre (0 * (capacity_pre + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : (KnapsackInputsBounded weights_l values_l n_pre capacity_pre )) ,
  (IntArray.undef_full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre (capacity_pre + 1 ) dp_l 0 ) ”
  &&  (IntArray.seg dp_pre 0 (0 * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg dp_pre (0 * (capacity_pre + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
).

Definition zeroOneKnapsack_entail_wit_2 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i )) ,
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
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + 0 ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + 0 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i )) ,
  (IntArray.seg dp_pre 0 (i * width ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i 0 ) ”
  &&  (IntArray.seg dp_pre 0 ((i * width ) + 0 ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_3 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (width <= INT_MAX)) (PreH4 : (capacity_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (((i * width ) + j ) <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (width >= INT_MIN)) (PreH10 : (capacity_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : (j <= capacity_pre)) (PreH14 : (width = (capacity_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 300)) (PreH17 : (0 <= capacity_pre)) (PreH18 : (capacity_pre <= 300)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= (capacity_pre + 1 ))) (PreH23 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  TT && emp 
|--
  “ (((i * (capacity_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_3_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (width <= INT_MAX)) (PreH4 : (capacity_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (((i * width ) + j ) <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (width >= INT_MIN)) (PreH10 : (capacity_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : (j <= capacity_pre)) (PreH14 : (width = (capacity_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 300)) (PreH17 : (0 <= capacity_pre)) (PreH18 : (capacity_pre <= 300)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= (capacity_pre + 1 ))) (PreH23 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (((i * (capacity_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))
.

Definition zeroOneKnapsack_entail_wit_4 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
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
.

Definition zeroOneKnapsack_entail_wit_5 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (((i * width ) + j ) <= INT_MAX)) (PreH4 : (((i * width ) + j ) >= INT_MIN)) (PreH5 : (j <> 0)) (PreH6 : (i <> 0)) (PreH7 : (0 <= ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (width <= INT_MAX)) (PreH12 : (capacity_pre <= INT_MAX)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (width >= INT_MIN)) (PreH17 : (capacity_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (j <= capacity_pre)) (PreH20 : (width = (capacity_pre + 1 ))) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 300)) (PreH23 : (0 <= capacity_pre)) (PreH24 : (capacity_pre <= 300)) (PreH25 : (0 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (0 <= j)) (PreH28 : (j <= (capacity_pre + 1 ))) (PreH29 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((i - 1 ) <= INT_MAX)) (PreH2 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH3 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH4 : ((i - 1 ) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH7 : (0 <= (i - 1 ))) (PreH8 : ((i - 1 ) < n_pre)) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : (((i * width ) + j ) >= INT_MIN)) (PreH11 : (j <> 0)) (PreH12 : (i <> 0)) (PreH13 : (0 <= ((i * width ) + j ))) (PreH14 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (j <= INT_MAX)) (PreH16 : (i <= INT_MAX)) (PreH17 : (width <= INT_MAX)) (PreH18 : (capacity_pre <= INT_MAX)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (j >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (width >= INT_MIN)) (PreH23 : (capacity_pre >= INT_MIN)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= capacity_pre)) (PreH26 : (width = (capacity_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 300)) (PreH29 : (0 <= capacity_pre)) (PreH30 : (capacity_pre <= 300)) (PreH31 : (0 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (0 <= j)) (PreH34 : (j <= (capacity_pre + 1 ))) (PreH35 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  TT && emp 
|--
  “ ((((i - 1 ) * (capacity_pre + 1 ) ) + j ) < ((i * (capacity_pre + 1 ) ) + j )) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_5_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((i - 1 ) <= INT_MAX)) (PreH2 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH3 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH4 : ((i - 1 ) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH7 : (0 <= (i - 1 ))) (PreH8 : ((i - 1 ) < n_pre)) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : (((i * width ) + j ) >= INT_MIN)) (PreH11 : (j <> 0)) (PreH12 : (i <> 0)) (PreH13 : (0 <= ((i * width ) + j ))) (PreH14 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (j <= INT_MAX)) (PreH16 : (i <= INT_MAX)) (PreH17 : (width <= INT_MAX)) (PreH18 : (capacity_pre <= INT_MAX)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (j >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (width >= INT_MIN)) (PreH23 : (capacity_pre >= INT_MIN)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= capacity_pre)) (PreH26 : (width = (capacity_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 300)) (PreH29 : (0 <= capacity_pre)) (PreH30 : (capacity_pre <= 300)) (PreH31 : (0 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (0 <= j)) (PreH34 : (j <= (capacity_pre + 1 ))) (PreH35 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((((i - 1 ) * (capacity_pre + 1 ) ) + j ) < ((i * (capacity_pre + 1 ) ) + j ))
.

Definition zeroOneKnapsack_entail_wit_6 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : ((i - 1 ) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (((i * width ) + j ) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : (j <> 0)) (PreH15 : (i <> 0)) (PreH16 : (0 <= ((i * width ) + j ))) (PreH17 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1 ))) (PreH30 : (0 <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : (0 <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : (0 <= i)) (PreH35 : (i <= n_pre)) (PreH36 : (0 <= j)) (PreH37 : (j <= (capacity_pre + 1 ))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH2 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH3 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH4 : (0 <= (((i - 1 ) * width ) + j ))) (PreH5 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH6 : ((i - 1 ) <= INT_MAX)) (PreH7 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH8 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH9 : ((i - 1 ) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH11 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (((i * width ) + j ) <= INT_MAX)) (PreH15 : (((i * width ) + j ) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  TT && emp 
|--
  “ ((((i - 1 ) * (capacity_pre + 1 ) ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * (capacity_pre + 1 ) ) + j )) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_6_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH2 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH3 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH4 : (0 <= (((i - 1 ) * width ) + j ))) (PreH5 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH6 : ((i - 1 ) <= INT_MAX)) (PreH7 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH8 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH9 : ((i - 1 ) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH11 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH12 : (0 <= (i - 1 ))) (PreH13 : ((i - 1 ) < n_pre)) (PreH14 : (((i * width ) + j ) <= INT_MAX)) (PreH15 : (((i * width ) + j ) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  ((((i - 1 ) * (capacity_pre + 1 ) ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * (capacity_pre + 1 ) ) + j ))
.

Definition zeroOneKnapsack_entail_wit_7_1 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_7_2 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_7_3 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : ((i - 1 ) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (((i * width ) + j ) <= INT_MAX)) (PreH18 : (((i * width ) + j ) >= INT_MIN)) (PreH19 : (j <> 0)) (PreH20 : (i <> 0)) (PreH21 : (0 <= ((i * width ) + j ))) (PreH22 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1 ))) (PreH35 : (0 <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : (0 <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : (0 <= i)) (PreH40 : (i <= n_pre)) (PreH41 : (0 <= j)) (PreH42 : (j <= (capacity_pre + 1 ))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : ((i - 1 ) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (((i * width ) + j ) <= INT_MAX)) (PreH18 : (((i * width ) + j ) >= INT_MIN)) (PreH19 : (j <> 0)) (PreH20 : (i <> 0)) (PreH21 : (0 <= ((i * width ) + j ))) (PreH22 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1 ))) (PreH35 : (0 <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : (0 <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : (0 <= i)) (PreH40 : (i <= n_pre)) (PreH41 : (0 <= j)) (PreH42 : (j <= (capacity_pre + 1 ))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) )) ((@nil Z))))) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_7_4 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : ((i - 1 ) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (((i * width ) + j ) <= INT_MAX)) (PreH18 : (((i * width ) + j ) >= INT_MIN)) (PreH19 : (j <> 0)) (PreH20 : (i <> 0)) (PreH21 : (0 <= ((i * width ) + j ))) (PreH22 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1 ))) (PreH35 : (0 <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : (0 <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : (0 <= i)) (PreH40 : (i <= n_pre)) (PreH41 : (0 <= j)) (PreH42 : (j <= (capacity_pre + 1 ))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : ((i - 1 ) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (((i * width ) + j ) <= INT_MAX)) (PreH18 : (((i * width ) + j ) >= INT_MIN)) (PreH19 : (j <> 0)) (PreH20 : (i <> 0)) (PreH21 : (0 <= ((i * width ) + j ))) (PreH22 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1 ))) (PreH35 : (0 <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : (0 <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : (0 <= i)) (PreH40 : (i <= n_pre)) (PreH41 : (0 <= j)) (PreH42 : (j <= (capacity_pre + 1 ))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0)) ((@nil Z))))) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_7_5 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) > j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : ((i - 1 ) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (((i * width ) + j ) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : (j <> 0)) (PreH15 : (i <> 0)) (PreH16 : (0 <= ((i * width ) + j ))) (PreH17 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1 ))) (PreH30 : (0 <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : (0 <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : (0 <= i)) (PreH35 : (i <= n_pre)) (PreH36 : (0 <= j)) (PreH37 : (j <= (capacity_pre + 1 ))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) > j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : ((i - 1 ) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (((i * width ) + j ) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : (j <> 0)) (PreH15 : (i <> 0)) (PreH16 : (0 <= ((i * width ) + j ))) (PreH17 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1 ))) (PreH30 : (0 <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : (0 <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : (0 <= i)) (PreH35 : (i <= n_pre)) (PreH36 : (0 <= j)) (PreH37 : (j <= (capacity_pre + 1 ))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0)) ((@nil Z))))) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg dp_pre 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_8 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
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
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l (i + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i + 1 ) * width ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i + 1 ) * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i j )) ,
  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l (i + 1 ) ) ”
  &&  (IntArray.seg dp_pre 0 ((i + 1 ) * width ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i + 1 ) * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
).

Definition zeroOneKnapsack_entail_wit_9 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i > n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 (i * width ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
) \/
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i > n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (KnapsackRowsAnnotationState weights_l values_l n_pre capacity_pre width dp_l_2 i )) ,
  (IntArray.seg dp_pre 0 (i * width ) dp_l_2 )
  **  (IntArray.undef_seg dp_pre (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ”
  &&  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_10 := 
(
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
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
  “ (0 <= ((n_pre * width ) + capacity_pre )) ” 
  &&  “ (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width <= INT_MAX)) (PreH2 : (capacity_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (width >= INT_MIN)) (PreH5 : (capacity_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (width = (capacity_pre + 1 ))) (PreH8 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  TT && emp 
|--
  “ (((n_pre * (capacity_pre + 1 ) ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (0 <= ((n_pre * (capacity_pre + 1 ) ) + capacity_pre )) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_10_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width <= INT_MAX)) (PreH2 : (capacity_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (width >= INT_MIN)) (PreH5 : (capacity_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (width = (capacity_pre + 1 ))) (PreH8 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  (((n_pre * (capacity_pre + 1 ) ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))
.

Definition zeroOneKnapsack_entail_wit_10_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width <= INT_MAX)) (PreH2 : (capacity_pre <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (width >= INT_MIN)) (PreH5 : (capacity_pre >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (width = (capacity_pre + 1 ))) (PreH8 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  (0 <= ((n_pre * (capacity_pre + 1 ) ) + capacity_pre ))
.

Definition zeroOneKnapsack_return_wit_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l_2 (Znth ((n_pre * width ) + capacity_pre ) dp_l_2 0) )) ,
  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l_2 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l_2 0) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
.

Definition zeroOneKnapsack_partial_solve_wit_1 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (i = 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  (((dp_pre + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
.

Definition zeroOneKnapsack_partial_solve_wit_2 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (j = 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  (((dp_pre + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
.

Definition zeroOneKnapsack_partial_solve_wit_3 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (((i * width ) + j ) <= INT_MAX)) (PreH4 : (((i * width ) + j ) >= INT_MIN)) (PreH5 : (j <> 0)) (PreH6 : (i <> 0)) (PreH7 : (0 <= ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (width <= INT_MAX)) (PreH12 : (capacity_pre <= INT_MAX)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (width >= INT_MIN)) (PreH17 : (capacity_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (j <= capacity_pre)) (PreH20 : (width = (capacity_pre + 1 ))) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 300)) (PreH23 : (0 <= capacity_pre)) (PreH24 : (capacity_pre <= 300)) (PreH25 : (0 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (0 <= j)) (PreH28 : (j <= (capacity_pre + 1 ))) (PreH29 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  (((weights_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.missing_i weights_pre (i - 1 ) 0 n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_partial_solve_wit_4 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (i - 1 ))) (PreH2 : ((i - 1 ) < n_pre)) (PreH3 : (((i * width ) + j ) <= INT_MAX)) (PreH4 : (((i * width ) + j ) >= INT_MIN)) (PreH5 : (j <> 0)) (PreH6 : (i <> 0)) (PreH7 : (0 <= ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH9 : (j <= INT_MAX)) (PreH10 : (i <= INT_MAX)) (PreH11 : (width <= INT_MAX)) (PreH12 : (capacity_pre <= INT_MAX)) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (width >= INT_MIN)) (PreH17 : (capacity_pre >= INT_MIN)) (PreH18 : (n_pre >= INT_MIN)) (PreH19 : (j <= capacity_pre)) (PreH20 : (width = (capacity_pre + 1 ))) (PreH21 : (0 <= n_pre)) (PreH22 : (n_pre <= 300)) (PreH23 : (0 <= capacity_pre)) (PreH24 : (capacity_pre <= 300)) (PreH25 : (0 <= i)) (PreH26 : (i <= n_pre)) (PreH27 : (0 <= j)) (PreH28 : (j <= (capacity_pre + 1 ))) (PreH29 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  (((values_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.missing_i values_pre (i - 1 ) 0 n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_partial_solve_wit_5 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : ((i - 1 ) <= INT_MAX)) (PreH4 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH6 : ((i - 1 ) >= INT_MIN)) (PreH7 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH9 : (0 <= (i - 1 ))) (PreH10 : ((i - 1 ) < n_pre)) (PreH11 : (((i * width ) + j ) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : (j <> 0)) (PreH14 : (i <> 0)) (PreH15 : (0 <= ((i * width ) + j ))) (PreH16 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH17 : (j <= INT_MAX)) (PreH18 : (i <= INT_MAX)) (PreH19 : (width <= INT_MAX)) (PreH20 : (capacity_pre <= INT_MAX)) (PreH21 : (n_pre <= INT_MAX)) (PreH22 : (j >= INT_MIN)) (PreH23 : (i >= INT_MIN)) (PreH24 : (width >= INT_MIN)) (PreH25 : (capacity_pre >= INT_MIN)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= capacity_pre)) (PreH28 : (width = (capacity_pre + 1 ))) (PreH29 : (0 <= n_pre)) (PreH30 : (n_pre <= 300)) (PreH31 : (0 <= capacity_pre)) (PreH32 : (capacity_pre <= 300)) (PreH33 : (0 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (0 <= j)) (PreH36 : (j <= (capacity_pre + 1 ))) (PreH37 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  (((dp_pre + ((((i - 1 ) * width ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.missing_i dp_pre (((i - 1 ) * width ) + j ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_partial_solve_wit_6 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : ((i - 1 ) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (0 <= (i - 1 ))) (PreH15 : ((i - 1 ) < n_pre)) (PreH16 : (((i * width ) + j ) <= INT_MAX)) (PreH17 : (((i * width ) + j ) >= INT_MIN)) (PreH18 : (j <> 0)) (PreH19 : (i <> 0)) (PreH20 : (0 <= ((i * width ) + j ))) (PreH21 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH22 : (j <= INT_MAX)) (PreH23 : (i <= INT_MAX)) (PreH24 : (width <= INT_MAX)) (PreH25 : (capacity_pre <= INT_MAX)) (PreH26 : (n_pre <= INT_MAX)) (PreH27 : (j >= INT_MIN)) (PreH28 : (i >= INT_MIN)) (PreH29 : (width >= INT_MIN)) (PreH30 : (capacity_pre >= INT_MIN)) (PreH31 : (n_pre >= INT_MIN)) (PreH32 : (j <= capacity_pre)) (PreH33 : (width = (capacity_pre + 1 ))) (PreH34 : (0 <= n_pre)) (PreH35 : (n_pre <= 300)) (PreH36 : (0 <= capacity_pre)) (PreH37 : (capacity_pre <= 300)) (PreH38 : (0 <= i)) (PreH39 : (i <= n_pre)) (PreH40 : (0 <= j)) (PreH41 : (j <= (capacity_pre + 1 ))) (PreH42 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  (((dp_pre + ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) * sizeof(INT)))) # Int  |-> (Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0))
  **  (IntArray.missing_i dp_pre (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
.

Definition zeroOneKnapsack_partial_solve_wit_7 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : ((i - 1 ) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (((i * width ) + j ) <= INT_MAX)) (PreH18 : (((i * width ) + j ) >= INT_MIN)) (PreH19 : (j <> 0)) (PreH20 : (i <> 0)) (PreH21 : (0 <= ((i * width ) + j ))) (PreH22 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1 ))) (PreH35 : (0 <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : (0 <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : (0 <= i)) (PreH40 : (i <= n_pre)) (PreH41 : (0 <= j)) (PreH42 : (j <= (capacity_pre + 1 ))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  (((dp_pre + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition zeroOneKnapsack_partial_solve_wit_8 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : ((i - 1 ) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH15 : (0 <= (i - 1 ))) (PreH16 : ((i - 1 ) < n_pre)) (PreH17 : (((i * width ) + j ) <= INT_MAX)) (PreH18 : (((i * width ) + j ) >= INT_MIN)) (PreH19 : (j <> 0)) (PreH20 : (i <> 0)) (PreH21 : (0 <= ((i * width ) + j ))) (PreH22 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH23 : (j <= INT_MAX)) (PreH24 : (i <= INT_MAX)) (PreH25 : (width <= INT_MAX)) (PreH26 : (capacity_pre <= INT_MAX)) (PreH27 : (n_pre <= INT_MAX)) (PreH28 : (j >= INT_MIN)) (PreH29 : (i >= INT_MIN)) (PreH30 : (width >= INT_MIN)) (PreH31 : (capacity_pre >= INT_MIN)) (PreH32 : (n_pre >= INT_MIN)) (PreH33 : (j <= capacity_pre)) (PreH34 : (width = (capacity_pre + 1 ))) (PreH35 : (0 <= n_pre)) (PreH36 : (n_pre <= 300)) (PreH37 : (0 <= capacity_pre)) (PreH38 : (capacity_pre <= 300)) (PreH39 : (0 <= i)) (PreH40 : (i <= n_pre)) (PreH41 : (0 <= j)) (PreH42 : (j <= (capacity_pre + 1 ))) (PreH43 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  (((dp_pre + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition zeroOneKnapsack_partial_solve_wit_9 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) > j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : ((i - 1 ) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH10 : (0 <= (i - 1 ))) (PreH11 : ((i - 1 ) < n_pre)) (PreH12 : (((i * width ) + j ) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : (j <> 0)) (PreH15 : (i <> 0)) (PreH16 : (0 <= ((i * width ) + j ))) (PreH17 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1 ))) (PreH30 : (0 <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : (0 <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : (0 <= i)) (PreH35 : (i <= n_pre)) (PreH36 : (0 <= j)) (PreH37 : (j <= (capacity_pre + 1 ))) (PreH38 : (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j )) ,
  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg dp_pre ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  “ ((Znth (i - 1 ) weights_l 0) > j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < n_pre) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ (j <> 0) ” 
  &&  “ (i <> 0) ” 
  &&  “ (0 <= ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (j <= INT_MAX) ” 
  &&  “ (i <= INT_MAX) ” 
  &&  “ (width <= INT_MAX) ” 
  &&  “ (capacity_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (j >= INT_MIN) ” 
  &&  “ (i >= INT_MIN) ” 
  &&  “ (width >= INT_MIN) ” 
  &&  “ (capacity_pre >= INT_MIN) ” 
  &&  “ (n_pre >= INT_MIN) ” 
  &&  “ (j <= capacity_pre) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (capacity_pre + 1 )) ” 
  &&  “ (KnapsackRowAnnotationState weights_l values_l n_pre capacity_pre width dp_l i j ) ”
  &&  (((dp_pre + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.seg dp_pre 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
.

Definition zeroOneKnapsack_partial_solve_wit_10 := 
forall (dp_pre: Z) (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH2 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (width = (capacity_pre + 1 ))) (PreH4 : (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full dp_pre ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
|--
  “ (0 <= ((n_pre * width ) + capacity_pre )) ” 
  &&  “ (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ” 
  &&  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (KnapsackResultState weights_l values_l n_pre capacity_pre dp_l (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ”
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
Axiom proof_of_zeroOneKnapsack_safety_wit_27 : zeroOneKnapsack_safety_wit_27.
Axiom proof_of_zeroOneKnapsack_safety_wit_28 : zeroOneKnapsack_safety_wit_28.
Axiom proof_of_zeroOneKnapsack_safety_wit_29 : zeroOneKnapsack_safety_wit_29.
Axiom proof_of_zeroOneKnapsack_safety_wit_30 : zeroOneKnapsack_safety_wit_30.
Axiom proof_of_zeroOneKnapsack_entail_wit_1 : zeroOneKnapsack_entail_wit_1.
Axiom proof_of_zeroOneKnapsack_entail_wit_2 : zeroOneKnapsack_entail_wit_2.
Axiom proof_of_zeroOneKnapsack_entail_wit_3 : zeroOneKnapsack_entail_wit_3.
Axiom proof_of_zeroOneKnapsack_entail_wit_4 : zeroOneKnapsack_entail_wit_4.
Axiom proof_of_zeroOneKnapsack_entail_wit_5 : zeroOneKnapsack_entail_wit_5.
Axiom proof_of_zeroOneKnapsack_entail_wit_6 : zeroOneKnapsack_entail_wit_6.
Axiom proof_of_zeroOneKnapsack_entail_wit_7_1 : zeroOneKnapsack_entail_wit_7_1.
Axiom proof_of_zeroOneKnapsack_entail_wit_7_2 : zeroOneKnapsack_entail_wit_7_2.
Axiom proof_of_zeroOneKnapsack_entail_wit_7_3 : zeroOneKnapsack_entail_wit_7_3.
Axiom proof_of_zeroOneKnapsack_entail_wit_7_4 : zeroOneKnapsack_entail_wit_7_4.
Axiom proof_of_zeroOneKnapsack_entail_wit_7_5 : zeroOneKnapsack_entail_wit_7_5.
Axiom proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8.
Axiom proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9.
Axiom proof_of_zeroOneKnapsack_entail_wit_10 : zeroOneKnapsack_entail_wit_10.
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
