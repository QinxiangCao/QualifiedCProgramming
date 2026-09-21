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

(*----- Function zeroOneKnapsack -----*)

Definition zeroOneKnapsack_safety_wit_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH9 : (Forall (Z.le (0)) values_l )) (PreH10 : (Forall (Z.ge (10000)) values_l )) ,
  ((( &( "width" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "dp" ) ) 90601 )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  “ ((capacity_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (capacity_pre + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH9 : (Forall (Z.le (0)) values_l )) (PreH10 : (Forall (Z.ge (10000)) values_l )) ,
  ((( &( "width" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "dp" ) ) 90601 )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH9 : (Forall (Z.le (0)) values_l )) (PreH10 : (Forall (Z.ge (10000)) values_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "width" ) )) # Int  |-> (capacity_pre + 1 ))
  **  (IntArray.undef_full ( &( "dp" ) ) 90601 )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_4 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (width: Z) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (10000)) values_l )) (PreH12 : (Forall (Z.le (0)) dp_l )) (PreH13 : (Forall (Z.ge (4000000)) dp_l )) (PreH14 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l i )) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 (i * width ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_5 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) weights_l )) (PreH12 : (Forall (Z.le (0)) values_l )) (PreH13 : (Forall (Z.ge (10000)) values_l )) (PreH14 : (Forall (Z.le (0)) dp_l )) (PreH15 : (Forall (Z.ge (4000000)) dp_l )) (PreH16 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * width ) + j )) ”
.

Definition zeroOneKnapsack_safety_wit_6 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) weights_l )) (PreH12 : (Forall (Z.le (0)) values_l )) (PreH13 : (Forall (Z.ge (10000)) values_l )) (PreH14 : (Forall (Z.le (0)) dp_l )) (PreH15 : (Forall (Z.ge (4000000)) dp_l )) (PreH16 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((i * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * width )) ”
.

Definition zeroOneKnapsack_safety_wit_7 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= ((i * width ) + j ))) (PreH2 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (width <= INT_MAX)) (PreH6 : (capacity_pre <= INT_MAX)) (PreH7 : (n_pre <= INT_MAX)) (PreH8 : (j >= INT_MIN)) (PreH9 : (i >= INT_MIN)) (PreH10 : (width >= INT_MIN)) (PreH11 : (capacity_pre >= INT_MIN)) (PreH12 : (n_pre >= INT_MIN)) (PreH13 : (j <= capacity_pre)) (PreH14 : (width = (capacity_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 300)) (PreH17 : (0 <= capacity_pre)) (PreH18 : (capacity_pre <= 300)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= (capacity_pre + 1 ))) (PreH23 : (Forall (Z.le (1)) weights_l )) (PreH24 : (Forall (Z.le (0)) values_l )) (PreH25 : (Forall (Z.ge (10000)) values_l )) (PreH26 : (Forall (Z.le (0)) dp_l )) (PreH27 : (Forall (Z.ge (4000000)) dp_l )) (PreH28 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_8 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (Forall (Z.le (1)) weights_l )) (PreH25 : (Forall (Z.le (0)) values_l )) (PreH26 : (Forall (Z.ge (10000)) values_l )) (PreH27 : (Forall (Z.le (0)) dp_l )) (PreH28 : (Forall (Z.ge (4000000)) dp_l )) (PreH29 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_9 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i <> 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (Forall (Z.le (1)) weights_l )) (PreH25 : (Forall (Z.le (0)) values_l )) (PreH26 : (Forall (Z.ge (10000)) values_l )) (PreH27 : (Forall (Z.le (0)) dp_l )) (PreH28 : (Forall (Z.ge (4000000)) dp_l )) (PreH29 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_10 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l )) (PreH29 : (Forall (Z.ge (4000000)) dp_l )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition zeroOneKnapsack_safety_wit_11 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l )) (PreH29 : (Forall (Z.ge (4000000)) dp_l )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "item" ) )) # Int  |->_)
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_12 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l )) (PreH29 : (Forall (Z.ge (4000000)) dp_l )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "item" ) )) # Int  |->_)
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_13 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) <= INT_MAX)) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : (((i * width ) + j ) >= INT_MIN)) (PreH8 : ((i - 1 ) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH11 : (j <> 0)) (PreH12 : (i <> 0)) (PreH13 : (0 <= ((i * width ) + j ))) (PreH14 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (j <= INT_MAX)) (PreH16 : (i <= INT_MAX)) (PreH17 : (width <= INT_MAX)) (PreH18 : (capacity_pre <= INT_MAX)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (j >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (width >= INT_MIN)) (PreH23 : (capacity_pre >= INT_MIN)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= capacity_pre)) (PreH26 : (width = (capacity_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 300)) (PreH29 : (0 <= capacity_pre)) (PreH30 : (capacity_pre <= 300)) (PreH31 : (0 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (0 <= j)) (PreH34 : (j <= (capacity_pre + 1 ))) (PreH35 : (Forall (Z.le (1)) weights_l )) (PreH36 : (Forall (Z.le (0)) values_l )) (PreH37 : (Forall (Z.ge (10000)) values_l )) (PreH38 : (Forall (Z.le (0)) dp_l )) (PreH39 : (Forall (Z.ge (4000000)) dp_l )) (PreH40 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((((i - 1 ) * width ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - 1 ) * width ) + j )) ”
.

Definition zeroOneKnapsack_safety_wit_14 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) <= INT_MAX)) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : (((i * width ) + j ) >= INT_MIN)) (PreH8 : ((i - 1 ) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH11 : (j <> 0)) (PreH12 : (i <> 0)) (PreH13 : (0 <= ((i * width ) + j ))) (PreH14 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (j <= INT_MAX)) (PreH16 : (i <= INT_MAX)) (PreH17 : (width <= INT_MAX)) (PreH18 : (capacity_pre <= INT_MAX)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (j >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (width >= INT_MIN)) (PreH23 : (capacity_pre >= INT_MIN)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= capacity_pre)) (PreH26 : (width = (capacity_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 300)) (PreH29 : (0 <= capacity_pre)) (PreH30 : (capacity_pre <= 300)) (PreH31 : (0 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (0 <= j)) (PreH34 : (j <= (capacity_pre + 1 ))) (PreH35 : (Forall (Z.le (1)) weights_l )) (PreH36 : (Forall (Z.le (0)) values_l )) (PreH37 : (Forall (Z.ge (10000)) values_l )) (PreH38 : (Forall (Z.le (0)) dp_l )) (PreH39 : (Forall (Z.ge (4000000)) dp_l )) (PreH40 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (((i - 1 ) * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - 1 ) * width )) ”
.

Definition zeroOneKnapsack_safety_wit_15 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) <= INT_MAX)) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : (((i * width ) + j ) >= INT_MIN)) (PreH8 : ((i - 1 ) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH11 : (j <> 0)) (PreH12 : (i <> 0)) (PreH13 : (0 <= ((i * width ) + j ))) (PreH14 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (j <= INT_MAX)) (PreH16 : (i <= INT_MAX)) (PreH17 : (width <= INT_MAX)) (PreH18 : (capacity_pre <= INT_MAX)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (j >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (width >= INT_MIN)) (PreH23 : (capacity_pre >= INT_MIN)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= capacity_pre)) (PreH26 : (width = (capacity_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 300)) (PreH29 : (0 <= capacity_pre)) (PreH30 : (capacity_pre <= 300)) (PreH31 : (0 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (0 <= j)) (PreH34 : (j <= (capacity_pre + 1 ))) (PreH35 : (Forall (Z.le (1)) weights_l )) (PreH36 : (Forall (Z.le (0)) values_l )) (PreH37 : (Forall (Z.ge (10000)) values_l )) (PreH38 : (Forall (Z.le (0)) dp_l )) (PreH39 : (Forall (Z.ge (4000000)) dp_l )) (PreH40 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_16 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) <= INT_MAX)) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : (((i * width ) + j ) >= INT_MIN)) (PreH8 : ((i - 1 ) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH11 : (j <> 0)) (PreH12 : (i <> 0)) (PreH13 : (0 <= ((i * width ) + j ))) (PreH14 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (j <= INT_MAX)) (PreH16 : (i <= INT_MAX)) (PreH17 : (width <= INT_MAX)) (PreH18 : (capacity_pre <= INT_MAX)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (j >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (width >= INT_MIN)) (PreH23 : (capacity_pre >= INT_MIN)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= capacity_pre)) (PreH26 : (width = (capacity_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 300)) (PreH29 : (0 <= capacity_pre)) (PreH30 : (capacity_pre <= 300)) (PreH31 : (0 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (0 <= j)) (PreH34 : (j <= (capacity_pre + 1 ))) (PreH35 : (Forall (Z.le (1)) weights_l )) (PreH36 : (Forall (Z.le (0)) values_l )) (PreH37 : (Forall (Z.ge (10000)) values_l )) (PreH38 : (Forall (Z.le (0)) dp_l )) (PreH39 : (Forall (Z.ge (4000000)) dp_l )) (PreH40 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_17 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ”
.

Definition zeroOneKnapsack_safety_wit_18 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((j - (Znth (i - 1 ) weights_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - (Znth (i - 1 ) weights_l 0) )) ”
.

Definition zeroOneKnapsack_safety_wit_19 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (((i - 1 ) * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - 1 ) * width )) ”
.

Definition zeroOneKnapsack_safety_wit_20 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_21 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "prev" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition zeroOneKnapsack_safety_wit_22 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "with_val" ) )) # Int  |->_)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) )) ”
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "with_val" ) )) # Int  |->_)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) )) ”
).

Definition zeroOneKnapsack_safety_wit_22_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "with_val" ) )) # Int  |->_)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= INT_MAX) ”
.

Definition zeroOneKnapsack_safety_wit_22_split_goal_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "with_val" ) )) # Int  |->_)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((INT_MIN) <= ((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) )) ”
.

Definition zeroOneKnapsack_safety_wit_23 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (Forall (Z.le (1)) weights_l )) (PreH25 : (Forall (Z.le (0)) values_l )) (PreH26 : (Forall (Z.ge (10000)) values_l )) (PreH27 : (Forall (Z.le (0)) dp_l )) (PreH28 : (Forall (Z.ge (4000000)) dp_l )) (PreH29 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_24 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l )) (PreH29 : (Forall (Z.ge (4000000)) dp_l )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_25 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : ((i - 1 ) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH12 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : ((i - 1 ) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH16 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH17 : (j <> 0)) (PreH18 : (i <> 0)) (PreH19 : (0 <= ((i * width ) + j ))) (PreH20 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (j <= INT_MAX)) (PreH22 : (i <= INT_MAX)) (PreH23 : (width <= INT_MAX)) (PreH24 : (capacity_pre <= INT_MAX)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (j >= INT_MIN)) (PreH27 : (i >= INT_MIN)) (PreH28 : (width >= INT_MIN)) (PreH29 : (capacity_pre >= INT_MIN)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= capacity_pre)) (PreH32 : (width = (capacity_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 300)) (PreH35 : (0 <= capacity_pre)) (PreH36 : (capacity_pre <= 300)) (PreH37 : (0 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (0 <= j)) (PreH40 : (j <= (capacity_pre + 1 ))) (PreH41 : (Forall (Z.le (1)) weights_l )) (PreH42 : (Forall (Z.le (0)) values_l )) (PreH43 : (Forall (Z.ge (10000)) values_l )) (PreH44 : (Forall (Z.le (0)) dp_l )) (PreH45 : (Forall (Z.ge (4000000)) dp_l )) (PreH46 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_26 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : ((i - 1 ) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH12 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : ((i - 1 ) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH16 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH17 : (j <> 0)) (PreH18 : (i <> 0)) (PreH19 : (0 <= ((i * width ) + j ))) (PreH20 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (j <= INT_MAX)) (PreH22 : (i <= INT_MAX)) (PreH23 : (width <= INT_MAX)) (PreH24 : (capacity_pre <= INT_MAX)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (j >= INT_MIN)) (PreH27 : (i >= INT_MIN)) (PreH28 : (width >= INT_MIN)) (PreH29 : (capacity_pre >= INT_MIN)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= capacity_pre)) (PreH32 : (width = (capacity_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 300)) (PreH35 : (0 <= capacity_pre)) (PreH36 : (capacity_pre <= 300)) (PreH37 : (0 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (0 <= j)) (PreH40 : (j <= (capacity_pre + 1 ))) (PreH41 : (Forall (Z.le (1)) weights_l )) (PreH42 : (Forall (Z.le (0)) values_l )) (PreH43 : (Forall (Z.ge (10000)) values_l )) (PreH44 : (Forall (Z.le (0)) dp_l )) (PreH45 : (Forall (Z.ge (4000000)) dp_l )) (PreH46 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_27 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) > j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) <= INT_MAX)) (PreH5 : ((i - 1 ) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH7 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH8 : (((i * width ) + j ) >= INT_MIN)) (PreH9 : ((i - 1 ) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH11 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH12 : (j <> 0)) (PreH13 : (i <> 0)) (PreH14 : (0 <= ((i * width ) + j ))) (PreH15 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (width <= INT_MAX)) (PreH19 : (capacity_pre <= INT_MAX)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (width >= INT_MIN)) (PreH24 : (capacity_pre >= INT_MIN)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= capacity_pre)) (PreH27 : (width = (capacity_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 300)) (PreH30 : (0 <= capacity_pre)) (PreH31 : (capacity_pre <= 300)) (PreH32 : (0 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (0 <= j)) (PreH35 : (j <= (capacity_pre + 1 ))) (PreH36 : (Forall (Z.le (1)) weights_l )) (PreH37 : (Forall (Z.le (0)) values_l )) (PreH38 : (Forall (Z.ge (10000)) values_l )) (PreH39 : (Forall (Z.le (0)) dp_l )) (PreH40 : (Forall (Z.ge (4000000)) dp_l )) (PreH41 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_28 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) weights_l )) (PreH12 : (Forall (Z.le (0)) values_l )) (PreH13 : (Forall (Z.ge (10000)) values_l )) (PreH14 : (Forall (Z.le (0)) dp_l )) (PreH15 : (Forall (Z.ge (4000000)) dp_l )) (PreH16 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition zeroOneKnapsack_safety_wit_29 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) (PreH7 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH8 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (((n_pre * width ) + capacity_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n_pre * width ) + capacity_pre )) ”
.

Definition zeroOneKnapsack_safety_wit_30 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) (PreH7 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH8 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((n_pre * width ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * width )) ”
.

Definition zeroOneKnapsack_entail_wit_1 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH9 : (Forall (Z.le (0)) values_l )) (PreH10 : (Forall (Z.ge (10000)) values_l )) ,
  (IntArray.undef_full ( &( "dp" ) ) 90601 )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  EX (dp_l: (@list Z)) ,
  “ ((capacity_pre + 1 ) = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 (0 * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (0 * (capacity_pre + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 300)) (PreH3 : (0 <= capacity_pre)) (PreH4 : (capacity_pre <= 300)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (values_l)) = n_pre)) (PreH7 : (Forall (Z.le (1)) weights_l )) (PreH8 : (Forall (Z.ge ((capacity_pre + 1 ))) weights_l )) (PreH9 : (Forall (Z.le (0)) values_l )) (PreH10 : (Forall (Z.ge (10000)) values_l )) ,
  (IntArray.undef_full ( &( "dp" ) ) 90601 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l 0 ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 (0 * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) (0 * (capacity_pre + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
).

Definition zeroOneKnapsack_entail_wit_2 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (10000)) values_l )) (PreH12 : (Forall (Z.le (0)) dp_l_2 )) (PreH13 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH14 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 i )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 (i * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i 0 ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + 0 ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + 0 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i <= n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (10000)) values_l )) (PreH12 : (Forall (Z.le (0)) dp_l_2 )) (PreH13 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH14 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 i )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (i * width ) dp_l_2 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i 0 ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + 0 ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_3 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) weights_l )) (PreH12 : (Forall (Z.le (0)) values_l )) (PreH13 : (Forall (Z.ge (10000)) values_l )) (PreH14 : (Forall (Z.le (0)) dp_l )) (PreH15 : (Forall (Z.ge (4000000)) dp_l )) (PreH16 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (width <= INT_MAX)) (PreH4 : (capacity_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (((i * width ) + j ) <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (width >= INT_MIN)) (PreH10 : (capacity_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : (j <= capacity_pre)) (PreH14 : (width = (capacity_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 300)) (PreH17 : (0 <= capacity_pre)) (PreH18 : (capacity_pre <= 300)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= (capacity_pre + 1 ))) (PreH23 : (Forall (Z.le (1)) weights_l )) (PreH24 : (Forall (Z.le (0)) values_l )) (PreH25 : (Forall (Z.ge (10000)) values_l )) (PreH26 : (Forall (Z.le (0)) dp_l )) (PreH27 : (Forall (Z.ge (4000000)) dp_l )) (PreH28 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  TT && emp 
|--
  “ (((i * (capacity_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_3_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (width <= INT_MAX)) (PreH4 : (capacity_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (((i * width ) + j ) <= INT_MAX)) (PreH7 : (j >= INT_MIN)) (PreH8 : (i >= INT_MIN)) (PreH9 : (width >= INT_MIN)) (PreH10 : (capacity_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : (j <= capacity_pre)) (PreH14 : (width = (capacity_pre + 1 ))) (PreH15 : (0 <= n_pre)) (PreH16 : (n_pre <= 300)) (PreH17 : (0 <= capacity_pre)) (PreH18 : (capacity_pre <= 300)) (PreH19 : (0 <= i)) (PreH20 : (i <= n_pre)) (PreH21 : (0 <= j)) (PreH22 : (j <= (capacity_pre + 1 ))) (PreH23 : (Forall (Z.le (1)) weights_l )) (PreH24 : (Forall (Z.le (0)) values_l )) (PreH25 : (Forall (Z.ge (10000)) values_l )) (PreH26 : (Forall (Z.le (0)) dp_l )) (PreH27 : (Forall (Z.ge (4000000)) dp_l )) (PreH28 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (((i * (capacity_pre + 1 ) ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))
.

Definition zeroOneKnapsack_entail_wit_4 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l )) (PreH29 : (Forall (Z.ge (4000000)) dp_l )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((i * width ) + j ) <= INT_MAX)) (PreH2 : ((i - 1 ) <= INT_MAX)) (PreH3 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH4 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH5 : (((i * width ) + j ) >= INT_MIN)) (PreH6 : ((i - 1 ) >= INT_MIN)) (PreH7 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH9 : (j <> 0)) (PreH10 : (i <> 0)) (PreH11 : (0 <= ((i * width ) + j ))) (PreH12 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH13 : (j <= INT_MAX)) (PreH14 : (i <= INT_MAX)) (PreH15 : (width <= INT_MAX)) (PreH16 : (capacity_pre <= INT_MAX)) (PreH17 : (n_pre <= INT_MAX)) (PreH18 : (j >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (width >= INT_MIN)) (PreH21 : (capacity_pre >= INT_MIN)) (PreH22 : (n_pre >= INT_MIN)) (PreH23 : (j <= capacity_pre)) (PreH24 : (width = (capacity_pre + 1 ))) (PreH25 : (0 <= n_pre)) (PreH26 : (n_pre <= 300)) (PreH27 : (0 <= capacity_pre)) (PreH28 : (capacity_pre <= 300)) (PreH29 : (0 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : (0 <= j)) (PreH32 : (j <= (capacity_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.le (0)) values_l )) (PreH35 : (Forall (Z.ge (10000)) values_l )) (PreH36 : (Forall (Z.le (0)) dp_l )) (PreH37 : (Forall (Z.ge (4000000)) dp_l )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  TT && emp 
|--
  “ ((((i - 1 ) * (capacity_pre + 1 ) ) + j ) < ((i * (capacity_pre + 1 ) ) + j )) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_4_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((i * width ) + j ) <= INT_MAX)) (PreH2 : ((i - 1 ) <= INT_MAX)) (PreH3 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH4 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH5 : (((i * width ) + j ) >= INT_MIN)) (PreH6 : ((i - 1 ) >= INT_MIN)) (PreH7 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH8 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH9 : (j <> 0)) (PreH10 : (i <> 0)) (PreH11 : (0 <= ((i * width ) + j ))) (PreH12 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH13 : (j <= INT_MAX)) (PreH14 : (i <= INT_MAX)) (PreH15 : (width <= INT_MAX)) (PreH16 : (capacity_pre <= INT_MAX)) (PreH17 : (n_pre <= INT_MAX)) (PreH18 : (j >= INT_MIN)) (PreH19 : (i >= INT_MIN)) (PreH20 : (width >= INT_MIN)) (PreH21 : (capacity_pre >= INT_MIN)) (PreH22 : (n_pre >= INT_MIN)) (PreH23 : (j <= capacity_pre)) (PreH24 : (width = (capacity_pre + 1 ))) (PreH25 : (0 <= n_pre)) (PreH26 : (n_pre <= 300)) (PreH27 : (0 <= capacity_pre)) (PreH28 : (capacity_pre <= 300)) (PreH29 : (0 <= i)) (PreH30 : (i <= n_pre)) (PreH31 : (0 <= j)) (PreH32 : (j <= (capacity_pre + 1 ))) (PreH33 : (Forall (Z.le (1)) weights_l )) (PreH34 : (Forall (Z.le (0)) values_l )) (PreH35 : (Forall (Z.ge (10000)) values_l )) (PreH36 : (Forall (Z.le (0)) dp_l )) (PreH37 : (Forall (Z.ge (4000000)) dp_l )) (PreH38 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((((i - 1 ) * (capacity_pre + 1 ) ) + j ) < ((i * (capacity_pre + 1 ) ) + j ))
.

Definition zeroOneKnapsack_entail_wit_5 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) <= INT_MAX)) (PreH5 : ((i - 1 ) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH7 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH8 : (((i * width ) + j ) >= INT_MIN)) (PreH9 : ((i - 1 ) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH11 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH12 : (j <> 0)) (PreH13 : (i <> 0)) (PreH14 : (0 <= ((i * width ) + j ))) (PreH15 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (width <= INT_MAX)) (PreH19 : (capacity_pre <= INT_MAX)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (width >= INT_MIN)) (PreH24 : (capacity_pre >= INT_MIN)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= capacity_pre)) (PreH27 : (width = (capacity_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 300)) (PreH30 : (0 <= capacity_pre)) (PreH31 : (capacity_pre <= 300)) (PreH32 : (0 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (0 <= j)) (PreH35 : (j <= (capacity_pre + 1 ))) (PreH36 : (Forall (Z.le (1)) weights_l )) (PreH37 : (Forall (Z.le (0)) values_l )) (PreH38 : (Forall (Z.ge (10000)) values_l )) (PreH39 : (Forall (Z.le (0)) dp_l )) (PreH40 : (Forall (Z.ge (4000000)) dp_l )) (PreH41 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
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
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "width" ) )) # Int  |-> width)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "w" ) )) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  ((( &( "without" ) )) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.full values_pre n_pre values_l )
  **  ((( &( "v" ) )) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.full weights_pre n_pre weights_l )
  **  ((( &( "item" ) )) # Int  |-> (i - 1 ))
  **  ((( &( "idx" ) )) # Int  |-> ((i * width ) + j ))
  **  ((( &( "weights" ) )) # Ptr  |-> weights_pre)
  **  ((( &( "values" ) )) # Ptr  |-> values_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "capacity" ) )) # Int  |-> capacity_pre)
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH2 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH3 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH4 : (0 <= (((i - 1 ) * width ) + j ))) (PreH5 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH6 : (((i * width ) + j ) <= INT_MAX)) (PreH7 : ((i - 1 ) <= INT_MAX)) (PreH8 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH10 : (((i * width ) + j ) >= INT_MIN)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (j <> 0)) (PreH15 : (i <> 0)) (PreH16 : (0 <= ((i * width ) + j ))) (PreH17 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1 ))) (PreH30 : (0 <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : (0 <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : (0 <= i)) (PreH35 : (i <= n_pre)) (PreH36 : (0 <= j)) (PreH37 : (j <= (capacity_pre + 1 ))) (PreH38 : (Forall (Z.le (1)) weights_l )) (PreH39 : (Forall (Z.le (0)) values_l )) (PreH40 : (Forall (Z.ge (10000)) values_l )) (PreH41 : (Forall (Z.le (0)) dp_l )) (PreH42 : (Forall (Z.ge (4000000)) dp_l )) (PreH43 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  TT && emp 
|--
  “ ((((i - 1 ) * (capacity_pre + 1 ) ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * (capacity_pre + 1 ) ) + j )) ”
  &&  emp
).

Definition zeroOneKnapsack_entail_wit_5_split_goal_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH2 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH3 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH4 : (0 <= (((i - 1 ) * width ) + j ))) (PreH5 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH6 : (((i * width ) + j ) <= INT_MAX)) (PreH7 : ((i - 1 ) <= INT_MAX)) (PreH8 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH9 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH10 : (((i * width ) + j ) >= INT_MIN)) (PreH11 : ((i - 1 ) >= INT_MIN)) (PreH12 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH13 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH14 : (j <> 0)) (PreH15 : (i <> 0)) (PreH16 : (0 <= ((i * width ) + j ))) (PreH17 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH18 : (j <= INT_MAX)) (PreH19 : (i <= INT_MAX)) (PreH20 : (width <= INT_MAX)) (PreH21 : (capacity_pre <= INT_MAX)) (PreH22 : (n_pre <= INT_MAX)) (PreH23 : (j >= INT_MIN)) (PreH24 : (i >= INT_MIN)) (PreH25 : (width >= INT_MIN)) (PreH26 : (capacity_pre >= INT_MIN)) (PreH27 : (n_pre >= INT_MIN)) (PreH28 : (j <= capacity_pre)) (PreH29 : (width = (capacity_pre + 1 ))) (PreH30 : (0 <= n_pre)) (PreH31 : (n_pre <= 300)) (PreH32 : (0 <= capacity_pre)) (PreH33 : (capacity_pre <= 300)) (PreH34 : (0 <= i)) (PreH35 : (i <= n_pre)) (PreH36 : (0 <= j)) (PreH37 : (j <= (capacity_pre + 1 ))) (PreH38 : (Forall (Z.le (1)) weights_l )) (PreH39 : (Forall (Z.le (0)) values_l )) (PreH40 : (Forall (Z.ge (10000)) values_l )) (PreH41 : (Forall (Z.le (0)) dp_l )) (PreH42 : (Forall (Z.ge (4000000)) dp_l )) (PreH43 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  ((((i - 1 ) * (capacity_pre + 1 ) ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * (capacity_pre + 1 ) ) + j ))
.

Definition zeroOneKnapsack_entail_wit_6_1 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (Forall (Z.le (1)) weights_l )) (PreH25 : (Forall (Z.le (0)) values_l )) (PreH26 : (Forall (Z.ge (10000)) values_l )) (PreH27 : (Forall (Z.le (0)) dp_l_2 )) (PreH28 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH29 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (Forall (Z.le (1)) weights_l )) (PreH25 : (Forall (Z.le (0)) values_l )) (PreH26 : (Forall (Z.ge (10000)) values_l )) (PreH27 : (Forall (Z.le (0)) dp_l_2 )) (PreH28 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH29 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_6_2 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l_2 )) (PreH29 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l_2 )) (PreH29 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_6_3 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : ((i - 1 ) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH12 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : ((i - 1 ) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH16 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH17 : (j <> 0)) (PreH18 : (i <> 0)) (PreH19 : (0 <= ((i * width ) + j ))) (PreH20 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (j <= INT_MAX)) (PreH22 : (i <= INT_MAX)) (PreH23 : (width <= INT_MAX)) (PreH24 : (capacity_pre <= INT_MAX)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (j >= INT_MIN)) (PreH27 : (i >= INT_MIN)) (PreH28 : (width >= INT_MIN)) (PreH29 : (capacity_pre >= INT_MIN)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= capacity_pre)) (PreH32 : (width = (capacity_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 300)) (PreH35 : (0 <= capacity_pre)) (PreH36 : (capacity_pre <= 300)) (PreH37 : (0 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (0 <= j)) (PreH40 : (j <= (capacity_pre + 1 ))) (PreH41 : (Forall (Z.le (1)) weights_l )) (PreH42 : (Forall (Z.le (0)) values_l )) (PreH43 : (Forall (Z.ge (10000)) values_l )) (PreH44 : (Forall (Z.le (0)) dp_l_2 )) (PreH45 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH46 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : ((i - 1 ) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH12 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : ((i - 1 ) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH16 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH17 : (j <> 0)) (PreH18 : (i <> 0)) (PreH19 : (0 <= ((i * width ) + j ))) (PreH20 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (j <= INT_MAX)) (PreH22 : (i <= INT_MAX)) (PreH23 : (width <= INT_MAX)) (PreH24 : (capacity_pre <= INT_MAX)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (j >= INT_MIN)) (PreH27 : (i >= INT_MIN)) (PreH28 : (width >= INT_MIN)) (PreH29 : (capacity_pre >= INT_MIN)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= capacity_pre)) (PreH32 : (width = (capacity_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 300)) (PreH35 : (0 <= capacity_pre)) (PreH36 : (capacity_pre <= 300)) (PreH37 : (0 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (0 <= j)) (PreH40 : (j <= (capacity_pre + 1 ))) (PreH41 : (Forall (Z.le (1)) weights_l )) (PreH42 : (Forall (Z.le (0)) values_l )) (PreH43 : (Forall (Z.ge (10000)) values_l )) (PreH44 : (Forall (Z.le (0)) dp_l_2 )) (PreH45 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH46 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) )) ((@nil Z))))) )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_6_4 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : ((i - 1 ) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH12 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : ((i - 1 ) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH16 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH17 : (j <> 0)) (PreH18 : (i <> 0)) (PreH19 : (0 <= ((i * width ) + j ))) (PreH20 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (j <= INT_MAX)) (PreH22 : (i <= INT_MAX)) (PreH23 : (width <= INT_MAX)) (PreH24 : (capacity_pre <= INT_MAX)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (j >= INT_MIN)) (PreH27 : (i >= INT_MIN)) (PreH28 : (width >= INT_MIN)) (PreH29 : (capacity_pre >= INT_MIN)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= capacity_pre)) (PreH32 : (width = (capacity_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 300)) (PreH35 : (0 <= capacity_pre)) (PreH36 : (capacity_pre <= 300)) (PreH37 : (0 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (0 <= j)) (PreH40 : (j <= (capacity_pre + 1 ))) (PreH41 : (Forall (Z.le (1)) weights_l )) (PreH42 : (Forall (Z.le (0)) values_l )) (PreH43 : (Forall (Z.ge (10000)) values_l )) (PreH44 : (Forall (Z.le (0)) dp_l_2 )) (PreH45 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH46 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l_2 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : ((i - 1 ) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH12 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : ((i - 1 ) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH16 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH17 : (j <> 0)) (PreH18 : (i <> 0)) (PreH19 : (0 <= ((i * width ) + j ))) (PreH20 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (j <= INT_MAX)) (PreH22 : (i <= INT_MAX)) (PreH23 : (width <= INT_MAX)) (PreH24 : (capacity_pre <= INT_MAX)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (j >= INT_MIN)) (PreH27 : (i >= INT_MIN)) (PreH28 : (width >= INT_MIN)) (PreH29 : (capacity_pre >= INT_MIN)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= capacity_pre)) (PreH32 : (width = (capacity_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 300)) (PreH35 : (0 <= capacity_pre)) (PreH36 : (capacity_pre <= 300)) (PreH37 : (0 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (0 <= j)) (PreH40 : (j <= (capacity_pre + 1 ))) (PreH41 : (Forall (Z.le (1)) weights_l )) (PreH42 : (Forall (Z.le (0)) values_l )) (PreH43 : (Forall (Z.ge (10000)) values_l )) (PreH44 : (Forall (Z.le (0)) dp_l_2 )) (PreH45 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH46 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0)) ((@nil Z))))) )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_6_5 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) > j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) <= INT_MAX)) (PreH5 : ((i - 1 ) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH7 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH8 : (((i * width ) + j ) >= INT_MIN)) (PreH9 : ((i - 1 ) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH11 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH12 : (j <> 0)) (PreH13 : (i <> 0)) (PreH14 : (0 <= ((i * width ) + j ))) (PreH15 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (width <= INT_MAX)) (PreH19 : (capacity_pre <= INT_MAX)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (width >= INT_MIN)) (PreH24 : (capacity_pre >= INT_MIN)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= capacity_pre)) (PreH27 : (width = (capacity_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 300)) (PreH30 : (0 <= capacity_pre)) (PreH31 : (capacity_pre <= 300)) (PreH32 : (0 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (0 <= j)) (PreH35 : (j <= (capacity_pre + 1 ))) (PreH36 : (Forall (Z.le (1)) weights_l )) (PreH37 : (Forall (Z.le (0)) values_l )) (PreH38 : (Forall (Z.ge (10000)) values_l )) (PreH39 : (Forall (Z.le (0)) dp_l_2 )) (PreH40 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH41 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + (j + 1 ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) > j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) <= INT_MAX)) (PreH5 : ((i - 1 ) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH7 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH8 : (((i * width ) + j ) >= INT_MIN)) (PreH9 : ((i - 1 ) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH11 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH12 : (j <> 0)) (PreH13 : (i <> 0)) (PreH14 : (0 <= ((i * width ) + j ))) (PreH15 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (width <= INT_MAX)) (PreH19 : (capacity_pre <= INT_MAX)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (width >= INT_MIN)) (PreH24 : (capacity_pre >= INT_MIN)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= capacity_pre)) (PreH27 : (width = (capacity_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 300)) (PreH30 : (0 <= capacity_pre)) (PreH31 : (capacity_pre <= 300)) (PreH32 : (0 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (0 <= j)) (PreH35 : (j <= (capacity_pre + 1 ))) (PreH36 : (Forall (Z.le (1)) weights_l )) (PreH37 : (Forall (Z.le (0)) values_l )) (PreH38 : (Forall (Z.ge (10000)) values_l )) (PreH39 : (Forall (Z.le (0)) dp_l_2 )) (PreH40 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH41 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (((i * width ) + j ) + 1 ) (app (dp_l_2) ((cons ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l_2 0)) ((@nil Z))))) )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i (j + 1 ) ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + (j + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_7 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) weights_l )) (PreH12 : (Forall (Z.le (0)) values_l )) (PreH13 : (Forall (Z.ge (10000)) values_l )) (PreH14 : (Forall (Z.le (0)) dp_l_2 )) (PreH15 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH16 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l (i + 1 ) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i + 1 ) * width ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i + 1 ) * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j > capacity_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= j)) (PreH10 : (j <= (capacity_pre + 1 ))) (PreH11 : (Forall (Z.le (1)) weights_l )) (PreH12 : (Forall (Z.le (0)) values_l )) (PreH13 : (Forall (Z.ge (10000)) values_l )) (PreH14 : (Forall (Z.le (0)) dp_l_2 )) (PreH15 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH16 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l_2 i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowsDone weights_l values_l capacity_pre dp_l (i + 1 ) ) ”
  &&  (IntArray.seg ( &( "dp" ) ) 0 ((i + 1 ) * width ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i + 1 ) * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
).

Definition zeroOneKnapsack_entail_wit_8 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i > n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (10000)) values_l )) (PreH12 : (Forall (Z.le (0)) dp_l_2 )) (PreH13 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH14 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 i )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 (i * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ” 
  &&  “ (0 <= ((n_pre * width ) + capacity_pre )) ” 
  &&  “ (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (width: Z) (PreH1 : (i > n_pre)) (PreH2 : (width = (capacity_pre + 1 ))) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 300)) (PreH5 : (0 <= capacity_pre)) (PreH6 : (capacity_pre <= 300)) (PreH7 : (0 <= i)) (PreH8 : (i <= (n_pre + 1 ))) (PreH9 : (Forall (Z.le (1)) weights_l )) (PreH10 : (Forall (Z.le (0)) values_l )) (PreH11 : (Forall (Z.ge (10000)) values_l )) (PreH12 : (Forall (Z.le (0)) dp_l_2 )) (PreH13 : (Forall (Z.ge (4000000)) dp_l_2 )) (PreH14 : (KnapsackRowsDone weights_l values_l capacity_pre dp_l_2 i )) ,
  (IntArray.seg ( &( "dp" ) ) 0 (i * width ) dp_l_2 )
  **  (IntArray.undef_seg ( &( "dp" ) ) (i * width ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ” 
  &&  “ (0 <= ((n_pre * width ) + capacity_pre )) ” 
  &&  “ (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ”
  &&  (IntArray.full ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
).

Definition zeroOneKnapsack_entail_wit_9 := 
(
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) (PreH7 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH8 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) ,
  (IntArray.full ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
  **  ((( &( "width" ) )) # Int  |-> width)
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_full ( &( "dp" ) ) 90601 )
  **  ((( &( "width" ) )) # Int  |->_)
) \/
(
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) (PreH7 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH8 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) ,
  (IntArray.full ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  (IntArray.undef_full ( &( "dp" ) ) 90601 )
).

Definition zeroOneKnapsack_entail_wit_9_split_goal_spatial := 
forall (capacity_pre: Z) (n_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) (PreH7 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH8 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) ,
  (IntArray.full ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  (IntArray.undef_full ( &( "dp" ) ) 90601 )
.

Definition zeroOneKnapsack_return_wit_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (result: Z) (PreH1 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre result )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
|--
  “ (KnapsackMaxValue weights_l values_l n_pre capacity_pre result ) ”
  &&  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
.

Definition zeroOneKnapsack_partial_solve_wit_1 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (i = 0)) (PreH2 : (0 <= ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH4 : (j <= INT_MAX)) (PreH5 : (i <= INT_MAX)) (PreH6 : (width <= INT_MAX)) (PreH7 : (capacity_pre <= INT_MAX)) (PreH8 : (n_pre <= INT_MAX)) (PreH9 : (j >= INT_MIN)) (PreH10 : (i >= INT_MIN)) (PreH11 : (width >= INT_MIN)) (PreH12 : (capacity_pre >= INT_MIN)) (PreH13 : (n_pre >= INT_MIN)) (PreH14 : (j <= capacity_pre)) (PreH15 : (width = (capacity_pre + 1 ))) (PreH16 : (0 <= n_pre)) (PreH17 : (n_pre <= 300)) (PreH18 : (0 <= capacity_pre)) (PreH19 : (capacity_pre <= 300)) (PreH20 : (0 <= i)) (PreH21 : (i <= n_pre)) (PreH22 : (0 <= j)) (PreH23 : (j <= (capacity_pre + 1 ))) (PreH24 : (Forall (Z.le (1)) weights_l )) (PreH25 : (Forall (Z.le (0)) values_l )) (PreH26 : (Forall (Z.ge (10000)) values_l )) (PreH27 : (Forall (Z.le (0)) dp_l )) (PreH28 : (Forall (Z.ge (4000000)) dp_l )) (PreH29 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  (((( &( "dp" ) ) + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Definition zeroOneKnapsack_partial_solve_wit_2 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j = 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l )) (PreH29 : (Forall (Z.ge (4000000)) dp_l )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  (((( &( "dp" ) ) + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Definition zeroOneKnapsack_partial_solve_wit_3 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l )) (PreH29 : (Forall (Z.ge (4000000)) dp_l )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (j <> 0) ” 
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  (((weights_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) weights_l 0))
  **  (IntArray.missing_i weights_pre (i - 1 ) 0 n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Definition zeroOneKnapsack_partial_solve_wit_4 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (j <> 0)) (PreH2 : (i <> 0)) (PreH3 : (0 <= ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH5 : (j <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (width <= INT_MAX)) (PreH8 : (capacity_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : (j >= INT_MIN)) (PreH11 : (i >= INT_MIN)) (PreH12 : (width >= INT_MIN)) (PreH13 : (capacity_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= capacity_pre)) (PreH16 : (width = (capacity_pre + 1 ))) (PreH17 : (0 <= n_pre)) (PreH18 : (n_pre <= 300)) (PreH19 : (0 <= capacity_pre)) (PreH20 : (capacity_pre <= 300)) (PreH21 : (0 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (0 <= j)) (PreH24 : (j <= (capacity_pre + 1 ))) (PreH25 : (Forall (Z.le (1)) weights_l )) (PreH26 : (Forall (Z.le (0)) values_l )) (PreH27 : (Forall (Z.ge (10000)) values_l )) (PreH28 : (Forall (Z.le (0)) dp_l )) (PreH29 : (Forall (Z.ge (4000000)) dp_l )) (PreH30 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (j <> 0) ” 
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  (((values_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) values_l 0))
  **  (IntArray.missing_i values_pre (i - 1 ) 0 n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Definition zeroOneKnapsack_partial_solve_wit_5 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + j ))) (PreH2 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH3 : (((i * width ) + j ) <= INT_MAX)) (PreH4 : ((i - 1 ) <= INT_MAX)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH7 : (((i * width ) + j ) >= INT_MIN)) (PreH8 : ((i - 1 ) >= INT_MIN)) (PreH9 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH11 : (j <> 0)) (PreH12 : (i <> 0)) (PreH13 : (0 <= ((i * width ) + j ))) (PreH14 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH15 : (j <= INT_MAX)) (PreH16 : (i <= INT_MAX)) (PreH17 : (width <= INT_MAX)) (PreH18 : (capacity_pre <= INT_MAX)) (PreH19 : (n_pre <= INT_MAX)) (PreH20 : (j >= INT_MIN)) (PreH21 : (i >= INT_MIN)) (PreH22 : (width >= INT_MIN)) (PreH23 : (capacity_pre >= INT_MIN)) (PreH24 : (n_pre >= INT_MIN)) (PreH25 : (j <= capacity_pre)) (PreH26 : (width = (capacity_pre + 1 ))) (PreH27 : (0 <= n_pre)) (PreH28 : (n_pre <= 300)) (PreH29 : (0 <= capacity_pre)) (PreH30 : (capacity_pre <= 300)) (PreH31 : (0 <= i)) (PreH32 : (i <= n_pre)) (PreH33 : (0 <= j)) (PreH34 : (j <= (capacity_pre + 1 ))) (PreH35 : (Forall (Z.le (1)) weights_l )) (PreH36 : (Forall (Z.le (0)) values_l )) (PreH37 : (Forall (Z.ge (10000)) values_l )) (PreH38 : (Forall (Z.le (0)) dp_l )) (PreH39 : (Forall (Z.ge (4000000)) dp_l )) (PreH40 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  (((( &( "dp" ) ) + ((((i - 1 ) * width ) + j ) * sizeof(INT)))) # Int  |-> (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) (((i - 1 ) * width ) + j ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Definition zeroOneKnapsack_partial_solve_wit_6 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH2 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH3 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH5 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH6 : (0 <= (((i - 1 ) * width ) + j ))) (PreH7 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH8 : (((i * width ) + j ) <= INT_MAX)) (PreH9 : ((i - 1 ) <= INT_MAX)) (PreH10 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH12 : (((i * width ) + j ) >= INT_MIN)) (PreH13 : ((i - 1 ) >= INT_MIN)) (PreH14 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH16 : (j <> 0)) (PreH17 : (i <> 0)) (PreH18 : (0 <= ((i * width ) + j ))) (PreH19 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH20 : (j <= INT_MAX)) (PreH21 : (i <= INT_MAX)) (PreH22 : (width <= INT_MAX)) (PreH23 : (capacity_pre <= INT_MAX)) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (j >= INT_MIN)) (PreH26 : (i >= INT_MIN)) (PreH27 : (width >= INT_MIN)) (PreH28 : (capacity_pre >= INT_MIN)) (PreH29 : (n_pre >= INT_MIN)) (PreH30 : (j <= capacity_pre)) (PreH31 : (width = (capacity_pre + 1 ))) (PreH32 : (0 <= n_pre)) (PreH33 : (n_pre <= 300)) (PreH34 : (0 <= capacity_pre)) (PreH35 : (capacity_pre <= 300)) (PreH36 : (0 <= i)) (PreH37 : (i <= n_pre)) (PreH38 : (0 <= j)) (PreH39 : (j <= (capacity_pre + 1 ))) (PreH40 : (Forall (Z.le (1)) weights_l )) (PreH41 : (Forall (Z.le (0)) values_l )) (PreH42 : (Forall (Z.ge (10000)) values_l )) (PreH43 : (Forall (Z.le (0)) dp_l )) (PreH44 : (Forall (Z.ge (4000000)) dp_l )) (PreH45 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  (((( &( "dp" ) ) + ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) * sizeof(INT)))) # Int  |-> (Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Definition zeroOneKnapsack_partial_solve_wit_7 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : ((i - 1 ) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH12 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : ((i - 1 ) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH16 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH17 : (j <> 0)) (PreH18 : (i <> 0)) (PreH19 : (0 <= ((i * width ) + j ))) (PreH20 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (j <= INT_MAX)) (PreH22 : (i <= INT_MAX)) (PreH23 : (width <= INT_MAX)) (PreH24 : (capacity_pre <= INT_MAX)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (j >= INT_MIN)) (PreH27 : (i >= INT_MIN)) (PreH28 : (width >= INT_MIN)) (PreH29 : (capacity_pre >= INT_MIN)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= capacity_pre)) (PreH32 : (width = (capacity_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 300)) (PreH35 : (0 <= capacity_pre)) (PreH36 : (capacity_pre <= 300)) (PreH37 : (0 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (0 <= j)) (PreH40 : (j <= (capacity_pre + 1 ))) (PreH41 : (Forall (Z.le (1)) weights_l )) (PreH42 : (Forall (Z.le (0)) values_l )) (PreH43 : (Forall (Z.ge (10000)) values_l )) (PreH44 : (Forall (Z.le (0)) dp_l )) (PreH45 : (Forall (Z.ge (4000000)) dp_l )) (PreH46 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) > (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  (((( &( "dp" ) ) + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Definition zeroOneKnapsack_partial_solve_wit_8 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0))) (PreH2 : (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ))) (PreH3 : ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j ))) (PreH4 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX)) (PreH5 : ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= j)) (PreH7 : (0 <= (((i - 1 ) * width ) + j ))) (PreH8 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH9 : (((i * width ) + j ) <= INT_MAX)) (PreH10 : ((i - 1 ) <= INT_MAX)) (PreH11 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH12 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH13 : (((i * width ) + j ) >= INT_MIN)) (PreH14 : ((i - 1 ) >= INT_MIN)) (PreH15 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH16 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH17 : (j <> 0)) (PreH18 : (i <> 0)) (PreH19 : (0 <= ((i * width ) + j ))) (PreH20 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH21 : (j <= INT_MAX)) (PreH22 : (i <= INT_MAX)) (PreH23 : (width <= INT_MAX)) (PreH24 : (capacity_pre <= INT_MAX)) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (j >= INT_MIN)) (PreH27 : (i >= INT_MIN)) (PreH28 : (width >= INT_MIN)) (PreH29 : (capacity_pre >= INT_MIN)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= capacity_pre)) (PreH32 : (width = (capacity_pre + 1 ))) (PreH33 : (0 <= n_pre)) (PreH34 : (n_pre <= 300)) (PreH35 : (0 <= capacity_pre)) (PreH36 : (capacity_pre <= 300)) (PreH37 : (0 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (0 <= j)) (PreH40 : (j <= (capacity_pre + 1 ))) (PreH41 : (Forall (Z.le (1)) weights_l )) (PreH42 : (Forall (Z.le (0)) values_l )) (PreH43 : (Forall (Z.ge (10000)) values_l )) (PreH44 : (Forall (Z.le (0)) dp_l )) (PreH45 : (Forall (Z.ge (4000000)) dp_l )) (PreH46 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (((Znth ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) - 0 ) dp_l 0) + (Znth (i - 1 ) values_l 0) ) <= (Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0)) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) )) ” 
  &&  “ ((((i - 1 ) * width ) + (j - (Znth (i - 1 ) weights_l 0) ) ) < ((i * width ) + j )) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) <= INT_MAX) ” 
  &&  “ ((Znth ((((i - 1 ) * width ) + j ) - 0 ) dp_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  (((( &( "dp" ) ) + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Definition zeroOneKnapsack_partial_solve_wit_9 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (i: Z) (width: Z) (PreH1 : ((Znth (i - 1 ) weights_l 0) > j)) (PreH2 : (0 <= (((i - 1 ) * width ) + j ))) (PreH3 : ((((i - 1 ) * width ) + j ) < ((i * width ) + j ))) (PreH4 : (((i * width ) + j ) <= INT_MAX)) (PreH5 : ((i - 1 ) <= INT_MAX)) (PreH6 : ((Znth (i - 1 ) weights_l 0) <= INT_MAX)) (PreH7 : ((Znth (i - 1 ) values_l 0) <= INT_MAX)) (PreH8 : (((i * width ) + j ) >= INT_MIN)) (PreH9 : ((i - 1 ) >= INT_MIN)) (PreH10 : ((Znth (i - 1 ) weights_l 0) >= INT_MIN)) (PreH11 : ((Znth (i - 1 ) values_l 0) >= INT_MIN)) (PreH12 : (j <> 0)) (PreH13 : (i <> 0)) (PreH14 : (0 <= ((i * width ) + j ))) (PreH15 : (((i * width ) + j ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) (PreH16 : (j <= INT_MAX)) (PreH17 : (i <= INT_MAX)) (PreH18 : (width <= INT_MAX)) (PreH19 : (capacity_pre <= INT_MAX)) (PreH20 : (n_pre <= INT_MAX)) (PreH21 : (j >= INT_MIN)) (PreH22 : (i >= INT_MIN)) (PreH23 : (width >= INT_MIN)) (PreH24 : (capacity_pre >= INT_MIN)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= capacity_pre)) (PreH27 : (width = (capacity_pre + 1 ))) (PreH28 : (0 <= n_pre)) (PreH29 : (n_pre <= 300)) (PreH30 : (0 <= capacity_pre)) (PreH31 : (capacity_pre <= 300)) (PreH32 : (0 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (0 <= j)) (PreH35 : (j <= (capacity_pre + 1 ))) (PreH36 : (Forall (Z.le (1)) weights_l )) (PreH37 : (Forall (Z.le (0)) values_l )) (PreH38 : (Forall (Z.ge (10000)) values_l )) (PreH39 : (Forall (Z.le (0)) dp_l )) (PreH40 : (Forall (Z.ge (4000000)) dp_l )) (PreH41 : (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j )) ,
  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((i * width ) + j ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ ((Znth (i - 1 ) weights_l 0) > j) ” 
  &&  “ (0 <= (((i - 1 ) * width ) + j )) ” 
  &&  “ ((((i - 1 ) * width ) + j ) < ((i * width ) + j )) ” 
  &&  “ (((i * width ) + j ) <= INT_MAX) ” 
  &&  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) <= INT_MAX) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) <= INT_MAX) ” 
  &&  “ (((i * width ) + j ) >= INT_MIN) ” 
  &&  “ ((i - 1 ) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) weights_l 0) >= INT_MIN) ” 
  &&  “ ((Znth (i - 1 ) values_l 0) >= INT_MIN) ” 
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
  &&  “ (Forall (Z.le (1)) weights_l ) ” 
  &&  “ (Forall (Z.le (0)) values_l ) ” 
  &&  “ (Forall (Z.ge (10000)) values_l ) ” 
  &&  “ (Forall (Z.le (0)) dp_l ) ” 
  &&  “ (Forall (Z.ge (4000000)) dp_l ) ” 
  &&  “ (KnapsackRowProgress weights_l values_l capacity_pre dp_l i j ) ”
  &&  (((( &( "dp" ) ) + (((i * width ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "dp" ) ) (((i * width ) + j ) + 1 ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) )
  **  (IntArray.seg ( &( "dp" ) ) 0 ((i * width ) + j ) dp_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Definition zeroOneKnapsack_partial_solve_wit_10 := 
forall (capacity_pre: Z) (n_pre: Z) (values_pre: Z) (weights_pre: Z) (values_l: (@list Z)) (weights_l: (@list Z)) (dp_l: (@list Z)) (width: Z) (PreH1 : (width = (capacity_pre + 1 ))) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 300)) (PreH4 : (0 <= capacity_pre)) (PreH5 : (capacity_pre <= 300)) (PreH6 : (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) )) (PreH7 : (0 <= ((n_pre * width ) + capacity_pre ))) (PreH8 : (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) ))) ,
  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.full ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
|--
  “ (width = (capacity_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 300) ” 
  &&  “ (0 <= capacity_pre) ” 
  &&  “ (capacity_pre <= 300) ” 
  &&  “ (KnapsackMaxValue weights_l values_l n_pre capacity_pre (Znth ((n_pre * width ) + capacity_pre ) dp_l 0) ) ” 
  &&  “ (0 <= ((n_pre * width ) + capacity_pre )) ” 
  &&  “ (((n_pre * width ) + capacity_pre ) < ((n_pre + 1 ) * (capacity_pre + 1 ) )) ”
  &&  (((( &( "dp" ) ) + (((n_pre * width ) + capacity_pre ) * sizeof(INT)))) # Int  |-> (Znth ((n_pre * width ) + capacity_pre ) dp_l 0))
  **  (IntArray.missing_i ( &( "dp" ) ) ((n_pre * width ) + capacity_pre ) 0 ((n_pre + 1 ) * (capacity_pre + 1 ) ) dp_l )
  **  (IntArray.full weights_pre n_pre weights_l )
  **  (IntArray.full values_pre n_pre values_l )
  **  (IntArray.undef_seg ( &( "dp" ) ) ((n_pre + 1 ) * (capacity_pre + 1 ) ) 90601 )
.

Module Type VC_Correct.


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
Axiom proof_of_zeroOneKnapsack_entail_wit_6_1 : zeroOneKnapsack_entail_wit_6_1.
Axiom proof_of_zeroOneKnapsack_entail_wit_6_2 : zeroOneKnapsack_entail_wit_6_2.
Axiom proof_of_zeroOneKnapsack_entail_wit_6_3 : zeroOneKnapsack_entail_wit_6_3.
Axiom proof_of_zeroOneKnapsack_entail_wit_6_4 : zeroOneKnapsack_entail_wit_6_4.
Axiom proof_of_zeroOneKnapsack_entail_wit_6_5 : zeroOneKnapsack_entail_wit_6_5.
Axiom proof_of_zeroOneKnapsack_entail_wit_7 : zeroOneKnapsack_entail_wit_7.
Axiom proof_of_zeroOneKnapsack_entail_wit_8 : zeroOneKnapsack_entail_wit_8.
Axiom proof_of_zeroOneKnapsack_entail_wit_9 : zeroOneKnapsack_entail_wit_9.
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
