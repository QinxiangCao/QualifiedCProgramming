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
Require Import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function coinChange -----*)

Definition coinChange_safety_wit_1 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_full dp_pre (amount_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_2 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_full dp_pre (amount_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition coinChange_safety_wit_3 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg dp_pre 0 1 (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg dp_pre 1 (amount_pre + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition coinChange_safety_wit_4 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l j )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg dp_pre 0 j dp_l )
  **  (IntArray.undef_seg dp_pre j (amount_pre + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_5 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l j )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.seg dp_pre 0 (j + 1 ) (app (dp_l) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (j + 1 ) (amount_pre + 1 ) )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition coinChange_safety_wit_6 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (DpPrefixZeroed dp_l (amount_pre + 1 ) )) (PreH7 : (DpReachableTable (@nil Z) dp_l (amount_pre + 1 ) )) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_7 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1 ))) (PreH14 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
|--
  “ ((j - coin ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - coin )) ”
.

Definition coinChange_safety_wit_8 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1 ))) (PreH14 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_9 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition coinChange_safety_wit_10 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) (replace_Znth (j) (1) (dp_l)) )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition coinChange_safety_wit_11 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l 0) = 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "coin" ) )) # Int  |-> coin)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition coinChange_safety_wit_12 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (coin: Z) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < coinsSize_pre)) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= INT_MAX)) (PreH11 : (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l (amount_pre + 1 ) )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition coinChange_safety_wit_13 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (0 <= res)) (PreH7 : (res <= amount_pre)) (PreH8 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH9 : (NoReachableAbove coins_l amount_pre res )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "res" ) )) # Int  |-> res)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_14 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (res > 0)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH10 : (NoReachableAbove coins_l amount_pre res )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "res" ) )) # Int  |-> res)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition coinChange_safety_wit_15 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l 0) = 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH11 : (NoReachableAbove coins_l amount_pre res )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
  **  ((( &( "coins" ) )) # Ptr  |-> coins_pre)
  **  ((( &( "coinsSize" ) )) # Int  |-> coinsSize_pre)
  **  ((( &( "amount" ) )) # Int  |-> amount_pre)
  **  ((( &( "dp" ) )) # Ptr  |-> dp_pre)
  **  ((( &( "res" ) )) # Int  |-> res)
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ ((res - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (res - 1 )) ”
.

Definition coinChange_entail_wit_1 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (((dp_pre + (0 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg dp_pre 1 (amount_pre + 1 ) )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg dp_pre 0 1 (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg dp_pre 1 (amount_pre + 1 ) )
) \/
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (((dp_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  (IntArray.seg dp_pre 0 1 (cons (1) ((@nil Z))) )
).

Definition coinChange_entail_wit_1_split_goal_spatial := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (((dp_pre + (0 * sizeof(INT)))) # Int  |-> 1)
|--
  (IntArray.seg dp_pre 0 1 (cons (1) ((@nil Z))) )
.

Definition coinChange_entail_wit_2 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg dp_pre 0 1 (cons (1) ((@nil Z))) )
  **  (IntArray.undef_seg dp_pre 1 (amount_pre + 1 ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (amount_pre + 1 )) ” 
  &&  “ (DpPrefixZeroed dp_l 1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg dp_pre 0 1 dp_l )
  **  (IntArray.undef_seg dp_pre 1 (amount_pre + 1 ) )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpPrefixZeroed (cons (1) ((@nil Z))) 1 ) ”
  &&  emp
).

Definition coinChange_entail_wit_2_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (DpPrefixZeroed (cons (1) ((@nil Z))) 1 )
.

Definition coinChange_entail_wit_3 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l_2 j )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.seg dp_pre 0 (j + 1 ) (app (dp_l_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg dp_pre (j + 1 ) (amount_pre + 1 ) )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (amount_pre + 1 )) ” 
  &&  “ (DpPrefixZeroed dp_l (j + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg dp_pre 0 (j + 1 ) dp_l )
  **  (IntArray.undef_seg dp_pre (j + 1 ) (amount_pre + 1 ) )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l_2 j )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpPrefixZeroed (app (dp_l_2) ((cons (0) ((@nil Z))))) (j + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_3_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l_2 j )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (DpPrefixZeroed (app (dp_l_2) ((cons (0) ((@nil Z))))) (j + 1 ) )
.

Definition coinChange_entail_wit_4 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l_2 j )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg dp_pre 0 j dp_l_2 )
  **  (IntArray.undef_seg dp_pre j (amount_pre + 1 ) )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (DpPrefixZeroed dp_l (amount_pre + 1 ) ) ” 
  &&  “ (DpReachableTable (@nil Z) dp_l (amount_pre + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l_2 j )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpReachableTable (@nil Z) dp_l_2 (amount_pre + 1 ) ) ” 
  &&  “ (DpPrefixZeroed dp_l_2 (amount_pre + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_4_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l_2 j )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (DpReachableTable (@nil Z) dp_l_2 (amount_pre + 1 ) )
.

Definition coinChange_entail_wit_4_split_goal_2 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l_2 j )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (DpPrefixZeroed dp_l_2 (amount_pre + 1 ) )
.

Definition coinChange_entail_wit_5 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (DpPrefixZeroed dp_l_2 (amount_pre + 1 ) )) (PreH7 : (DpReachableTable (@nil Z) dp_l_2 (amount_pre + 1 ) )) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= coinsSize_pre) ” 
  &&  “ (DpReachableTable (sublist (0) (0) (coins_l)) dp_l (amount_pre + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (DpPrefixZeroed dp_l_2 (amount_pre + 1 ) )) (PreH7 : (DpReachableTable (@nil Z) dp_l_2 (amount_pre + 1 ) )) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpReachableTable (sublist (0) (0) (coins_l)) dp_l_2 (amount_pre + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_5_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (DpPrefixZeroed dp_l_2 (amount_pre + 1 ) )) (PreH7 : (DpReachableTable (@nil Z) dp_l_2 (amount_pre + 1 ) )) (PreH8 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (DpReachableTable (sublist (0) (0) (coins_l)) dp_l_2 (amount_pre + 1 ) )
.

Definition coinChange_entail_wit_6 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i < coinsSize_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ ((Znth i coins_l 0) = (Znth i coins_l 0)) ” 
  &&  “ (1 <= (Znth i coins_l 0)) ” 
  &&  “ ((Znth i coins_l 0) <= INT_MAX) ” 
  &&  “ (DpReachableTable (sublist (0) (i) (coins_l)) dp_l (amount_pre + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i < coinsSize_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((Znth i coins_l 0) <= INT_MAX) ” 
  &&  “ (1 <= (Znth i coins_l 0)) ”
  &&  emp
).

Definition coinChange_entail_wit_6_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i < coinsSize_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  ((Znth i coins_l 0) <= INT_MAX)
.

Definition coinChange_entail_wit_6_split_goal_2 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i < coinsSize_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (1 <= (Znth i coins_l 0))
.

Definition coinChange_entail_wit_7 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (coin: Z) (PreH1 : (coin <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= amount_pre) ” 
  &&  “ (coin <= coin) ” 
  &&  “ (coin <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l coin amount_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (coin: Z) (PreH1 : (coin <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 coin amount_pre ) ”
  &&  emp
).

Definition coinChange_entail_wit_7_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (coin: Z) (PreH1 : (coin <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 coin amount_pre )
.

Definition coinChange_entail_wit_8_1 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) (replace_Znth (j) (1) (dp_l_2)) )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= amount_pre) ” 
  &&  “ (coin <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l (j + 1 ) amount_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin (replace_Znth (j) (1) (dp_l_2)) (j + 1 ) amount_pre ) ”
  &&  emp
).

Definition coinChange_entail_wit_8_1_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin (replace_Znth (j) (1) (dp_l_2)) (j + 1 ) amount_pre )
.

Definition coinChange_entail_wit_8_2 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) = 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= amount_pre) ” 
  &&  “ (coin <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l (j + 1 ) amount_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) = 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 (j + 1 ) amount_pre ) ”
  &&  emp
).

Definition coinChange_entail_wit_8_2_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l_2 0) = 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 (j + 1 ) amount_pre )
.

Definition coinChange_entail_wit_9_1 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (coin: Z) (PreH1 : (coin > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= INT_MAX) ” 
  &&  “ (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l (amount_pre + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (coin: Z) (PreH1 : (coin > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l_2 (amount_pre + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_9_1_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (coin: Z) (PreH1 : (coin > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= INT_MAX)) (PreH12 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH13 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l_2 (amount_pre + 1 ) )
.

Definition coinChange_entail_wit_9_2 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1 ))) (PreH14 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= INT_MAX) ” 
  &&  “ (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l (amount_pre + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1 ))) (PreH14 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l_2 (amount_pre + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_9_2_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j > amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1 ))) (PreH14 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l_2 j amount_pre )) (PreH15 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l_2 (amount_pre + 1 ) )
.

Definition coinChange_entail_wit_10 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (coin: Z) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < coinsSize_pre)) (PreH8 : (coin = (Znth i coins_l 0))) (PreH9 : (1 <= coin)) (PreH10 : (coin <= INT_MAX)) (PreH11 : (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH12 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= coinsSize_pre) ” 
  &&  “ (DpReachableTable (sublist (0) ((i + 1 )) (coins_l)) dp_l (amount_pre + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
.

Definition coinChange_entail_wit_11 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= amount_pre) ” 
  &&  “ (DpReachableTable coins_l dp_l (amount_pre + 1 ) ) ” 
  &&  “ (NoReachableAbove coins_l amount_pre amount_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (NoReachableAbove coins_l amount_pre amount_pre ) ” 
  &&  “ (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_11_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (NoReachableAbove coins_l amount_pre amount_pre )
.

Definition coinChange_entail_wit_11_split_goal_2 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (i: Z) (PreH1 : (i >= coinsSize_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l_2 (amount_pre + 1 ) )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < coinsSize_pre)) -> ((1 <= (Znth k_2 coins_l 0)) /\ ((Znth k_2 coins_l 0) <= INT_MAX)))) ,
  (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )
.

Definition coinChange_entail_wit_12 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l_2 0) = 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH11 : (NoReachableAbove coins_l amount_pre res )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= (res - 1 )) ” 
  &&  “ ((res - 1 ) <= amount_pre) ” 
  &&  “ (DpReachableTable coins_l dp_l (amount_pre + 1 ) ) ” 
  &&  “ (NoReachableAbove coins_l amount_pre (res - 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l_2 0) = 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH11 : (NoReachableAbove coins_l amount_pre res )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (NoReachableAbove coins_l amount_pre (res - 1 ) ) ”
  &&  emp
).

Definition coinChange_entail_wit_12_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l_2 0) = 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH11 : (NoReachableAbove coins_l amount_pre res )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (NoReachableAbove coins_l amount_pre (res - 1 ) )
.

Definition coinChange_entail_wit_13_1 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l_2 0) <> 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH11 : (NoReachableAbove coins_l amount_pre res )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= res) ” 
  &&  “ (res <= amount_pre) ” 
  &&  “ (DpReachableTable coins_l dp_l (amount_pre + 1 ) ) ” 
  &&  “ (NoReachableAbove coins_l amount_pre res ) ” 
  &&  “ (MaxReachableAmount coins_l amount_pre res ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l_2 0) <> 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH11 : (NoReachableAbove coins_l amount_pre res )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (MaxReachableAmount coins_l amount_pre res ) ”
  &&  emp
).

Definition coinChange_entail_wit_13_1_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : ((Znth res dp_l_2 0) <> 0)) (PreH2 : (res > 0)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= res)) (PreH9 : (res <= amount_pre)) (PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH11 : (NoReachableAbove coins_l amount_pre res )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (MaxReachableAmount coins_l amount_pre res )
.

Definition coinChange_entail_wit_13_2 := 
(
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : (res <= 0)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH10 : (NoReachableAbove coins_l amount_pre res )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= res) ” 
  &&  “ (res <= amount_pre) ” 
  &&  “ (DpReachableTable coins_l dp_l (amount_pre + 1 ) ) ” 
  &&  “ (NoReachableAbove coins_l amount_pre res ) ” 
  &&  “ (MaxReachableAmount coins_l amount_pre res ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
) \/
(
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : (res <= 0)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH10 : (NoReachableAbove coins_l amount_pre res )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (MaxReachableAmount coins_l amount_pre res ) ”
  &&  emp
).

Definition coinChange_entail_wit_13_2_split_goal_1 := 
forall (amount_pre: Z) (coinsSize_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : (res <= 0)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH10 : (NoReachableAbove coins_l amount_pre res )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (MaxReachableAmount coins_l amount_pre res )
.

Definition coinChange_return_wit_1 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l_2: (@list Z)) (res: Z) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : (0 <= res)) (PreH7 : (res <= amount_pre)) (PreH8 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1 ) )) (PreH9 : (NoReachableAbove coins_l amount_pre res )) (PreH10 : (MaxReachableAmount coins_l amount_pre res )) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l_2 )
|--
  EX (dp_l: (@list Z)) ,
  “ (MaxReachableAmount coins_l amount_pre res ) ” 
  &&  “ (DpReachableTable coins_l dp_l (amount_pre + 1 ) ) ”
  &&  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
.

Definition coinChange_partial_solve_wit_1 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (PreH1 : (0 <= coinsSize_pre)) (PreH2 : (coinsSize_pre <= 100000)) (PreH3 : (0 <= amount_pre)) (PreH4 : (amount_pre <= 100000)) (PreH5 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.undef_full dp_pre (amount_pre + 1 ) )
|--
  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (((dp_pre + (0 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre 1 (amount_pre + 1 ) )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
.

Definition coinChange_partial_solve_wit_2 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (amount_pre + 1 ))) (PreH9 : (DpPrefixZeroed dp_l j )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg dp_pre 0 j dp_l )
  **  (IntArray.undef_seg dp_pre j (amount_pre + 1 ) )
|--
  “ (j <= amount_pre) ” 
  &&  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j <= (amount_pre + 1 )) ” 
  &&  “ (DpPrefixZeroed dp_l j ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (((dp_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg dp_pre (j + 1 ) (amount_pre + 1 ) )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.seg dp_pre 0 j dp_l )
.

Definition coinChange_partial_solve_wit_3 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (i: Z) (PreH1 : (i < coinsSize_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= coinsSize_pre)) (PreH9 : (DpReachableTable (sublist (0) (i) (coins_l)) dp_l (amount_pre + 1 ) )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
|--
  “ (i < coinsSize_pre) ” 
  &&  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= coinsSize_pre) ” 
  &&  “ (DpReachableTable (sublist (0) (i) (coins_l)) dp_l (amount_pre + 1 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (((coins_pre + (i * sizeof(INT)))) # Int  |-> (Znth i coins_l 0))
  **  (IntArray.missing_i coins_pre i 0 coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
.

Definition coinChange_partial_solve_wit_4 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : (j <= amount_pre)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < coinsSize_pre)) (PreH9 : (coin = (Znth i coins_l 0))) (PreH10 : (1 <= coin)) (PreH11 : (coin <= amount_pre)) (PreH12 : (coin <= j)) (PreH13 : (j <= (amount_pre + 1 ))) (PreH14 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
|--
  “ (j <= amount_pre) ” 
  &&  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= amount_pre) ” 
  &&  “ (coin <= j) ” 
  &&  “ (j <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (((dp_pre + ((j - coin ) * sizeof(INT)))) # Int  |-> (Znth (j - coin ) dp_l 0))
  **  (IntArray.missing_i dp_pre (j - coin ) 0 (amount_pre + 1 ) dp_l )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
.

Definition coinChange_partial_solve_wit_5 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (j: Z) (coin: Z) (i: Z) (PreH1 : ((Znth (j - coin ) dp_l 0) <> 0)) (PreH2 : (j <= amount_pre)) (PreH3 : (0 <= coinsSize_pre)) (PreH4 : (coinsSize_pre <= 100000)) (PreH5 : (0 <= amount_pre)) (PreH6 : (amount_pre <= 100000)) (PreH7 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < coinsSize_pre)) (PreH10 : (coin = (Znth i coins_l 0))) (PreH11 : (1 <= coin)) (PreH12 : (coin <= amount_pre)) (PreH13 : (coin <= j)) (PreH14 : (j <= (amount_pre + 1 ))) (PreH15 : (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
|--
  “ ((Znth (j - coin ) dp_l 0) <> 0) ” 
  &&  “ (j <= amount_pre) ” 
  &&  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < coinsSize_pre) ” 
  &&  “ (coin = (Znth i coins_l 0)) ” 
  &&  “ (1 <= coin) ” 
  &&  “ (coin <= amount_pre) ” 
  &&  “ (coin <= j) ” 
  &&  “ (j <= (amount_pre + 1 )) ” 
  &&  “ (DpCoinInnerProgress (sublist (0) (i) (coins_l)) coin dp_l j amount_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (((dp_pre + (j * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i dp_pre j 0 (amount_pre + 1 ) dp_l )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
.

Definition coinChange_partial_solve_wit_6 := 
forall (dp_pre: Z) (amount_pre: Z) (coinsSize_pre: Z) (coins_pre: Z) (coins_l: (@list Z)) (dp_l: (@list Z)) (res: Z) (PreH1 : (res > 0)) (PreH2 : (0 <= coinsSize_pre)) (PreH3 : (coinsSize_pre <= 100000)) (PreH4 : (0 <= amount_pre)) (PreH5 : (amount_pre <= 100000)) (PreH6 : ((Zlength (coins_l)) = coinsSize_pre)) (PreH7 : (0 <= res)) (PreH8 : (res <= amount_pre)) (PreH9 : (DpReachableTable coins_l dp_l (amount_pre + 1 ) )) (PreH10 : (NoReachableAbove coins_l amount_pre res )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX)))) ,
  (IntArray.full coins_pre coinsSize_pre coins_l )
  **  (IntArray.full dp_pre (amount_pre + 1 ) dp_l )
|--
  “ (res > 0) ” 
  &&  “ (0 <= coinsSize_pre) ” 
  &&  “ (coinsSize_pre <= 100000) ” 
  &&  “ (0 <= amount_pre) ” 
  &&  “ (amount_pre <= 100000) ” 
  &&  “ ((Zlength (coins_l)) = coinsSize_pre) ” 
  &&  “ (0 <= res) ” 
  &&  “ (res <= amount_pre) ” 
  &&  “ (DpReachableTable coins_l dp_l (amount_pre + 1 ) ) ” 
  &&  “ (NoReachableAbove coins_l amount_pre res ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < coinsSize_pre)) -> ((1 <= (Znth k coins_l 0)) /\ ((Znth k coins_l 0) <= INT_MAX))) ”
  &&  (((dp_pre + (res * sizeof(INT)))) # Int  |-> (Znth res dp_l 0))
  **  (IntArray.missing_i dp_pre res 0 (amount_pre + 1 ) dp_l )
  **  (IntArray.full coins_pre coinsSize_pre coins_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_coinChange_safety_wit_1 : coinChange_safety_wit_1.
Axiom proof_of_coinChange_safety_wit_2 : coinChange_safety_wit_2.
Axiom proof_of_coinChange_safety_wit_3 : coinChange_safety_wit_3.
Axiom proof_of_coinChange_safety_wit_4 : coinChange_safety_wit_4.
Axiom proof_of_coinChange_safety_wit_5 : coinChange_safety_wit_5.
Axiom proof_of_coinChange_safety_wit_6 : coinChange_safety_wit_6.
Axiom proof_of_coinChange_safety_wit_7 : coinChange_safety_wit_7.
Axiom proof_of_coinChange_safety_wit_8 : coinChange_safety_wit_8.
Axiom proof_of_coinChange_safety_wit_9 : coinChange_safety_wit_9.
Axiom proof_of_coinChange_safety_wit_10 : coinChange_safety_wit_10.
Axiom proof_of_coinChange_safety_wit_11 : coinChange_safety_wit_11.
Axiom proof_of_coinChange_safety_wit_12 : coinChange_safety_wit_12.
Axiom proof_of_coinChange_safety_wit_13 : coinChange_safety_wit_13.
Axiom proof_of_coinChange_safety_wit_14 : coinChange_safety_wit_14.
Axiom proof_of_coinChange_safety_wit_15 : coinChange_safety_wit_15.
Axiom proof_of_coinChange_entail_wit_1 : coinChange_entail_wit_1.
Axiom proof_of_coinChange_entail_wit_2 : coinChange_entail_wit_2.
Axiom proof_of_coinChange_entail_wit_3 : coinChange_entail_wit_3.
Axiom proof_of_coinChange_entail_wit_4 : coinChange_entail_wit_4.
Axiom proof_of_coinChange_entail_wit_5 : coinChange_entail_wit_5.
Axiom proof_of_coinChange_entail_wit_6 : coinChange_entail_wit_6.
Axiom proof_of_coinChange_entail_wit_7 : coinChange_entail_wit_7.
Axiom proof_of_coinChange_entail_wit_8_1 : coinChange_entail_wit_8_1.
Axiom proof_of_coinChange_entail_wit_8_2 : coinChange_entail_wit_8_2.
Axiom proof_of_coinChange_entail_wit_9_1 : coinChange_entail_wit_9_1.
Axiom proof_of_coinChange_entail_wit_9_2 : coinChange_entail_wit_9_2.
Axiom proof_of_coinChange_entail_wit_10 : coinChange_entail_wit_10.
Axiom proof_of_coinChange_entail_wit_11 : coinChange_entail_wit_11.
Axiom proof_of_coinChange_entail_wit_12 : coinChange_entail_wit_12.
Axiom proof_of_coinChange_entail_wit_13_1 : coinChange_entail_wit_13_1.
Axiom proof_of_coinChange_entail_wit_13_2 : coinChange_entail_wit_13_2.
Axiom proof_of_coinChange_return_wit_1 : coinChange_return_wit_1.
Axiom proof_of_coinChange_partial_solve_wit_1 : coinChange_partial_solve_wit_1.
Axiom proof_of_coinChange_partial_solve_wit_2 : coinChange_partial_solve_wit_2.
Axiom proof_of_coinChange_partial_solve_wit_3 : coinChange_partial_solve_wit_3.
Axiom proof_of_coinChange_partial_solve_wit_4 : coinChange_partial_solve_wit_4.
Axiom proof_of_coinChange_partial_solve_wit_5 : coinChange_partial_solve_wit_5.
Axiom proof_of_coinChange_partial_solve_wit_6 : coinChange_partial_solve_wit_6.

End VC_Correct.
