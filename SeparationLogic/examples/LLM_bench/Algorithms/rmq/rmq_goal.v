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
Require Import SimpleC.EE.LLM_bench.Algorithms.rmq.rmq_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function build -----*)

Definition build_safety_wit_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st0)) = (n_pre * K_pre ))) (PreH9 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX)))) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (0 <= idx)) (PreH10 : (idx <= (n_pre * K_pre ))) (PreH11 : (STZeroPrefix st_l idx )) (PreH12 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((n_pre * K_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * K_pre )) ”
.

Definition build_safety_wit_3 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l idx )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_4 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l idx )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth (idx) (0) (st_l)) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition build_safety_wit_5 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (STZeroPrefix st_l (n_pre * K_pre ) )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_6 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= (i * K_pre ))) (PreH12 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH13 : (STBasePrefix l st_l K_pre n_pre i )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i * K_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * K_pre )) ”
.

Definition build_safety_wit_7 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (STBasePrefix l st_l K_pre n_pre (i + 1 ) )) (PreH12 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_safety_wit_8 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre 1 )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "half" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_9 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre 1 )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "half" ) )) # Int  |-> 1)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition build_safety_wit_10 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre 1 )) (PreH10 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> 2)
  **  ((( &( "half" ) )) # Int  |-> 1)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_11 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (j < K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j <= K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_12 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH16 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH17 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + len )) ”
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH16 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH17 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i + len ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + len )) ”
).

Definition build_safety_wit_12_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH16 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH17 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i + len ) <= INT_MAX) ”
.

Definition build_safety_wit_12_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : (i <= n_pre)) (PreH15 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH16 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH17 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= (i + len )) ”
.

Definition build_safety_wit_13 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((((i * K_pre ) + j ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i * K_pre ) + j ) - 1 )) ”
.

Definition build_safety_wit_14 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (((i * K_pre ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * K_pre ) + j )) ”
.

Definition build_safety_wit_15 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i * K_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * K_pre )) ”
.

Definition build_safety_wit_16 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_17 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((((i + half ) * K_pre ) + j ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((i + half ) * K_pre ) + j ) - 1 )) ”
.

Definition build_safety_wit_18 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((((i + half ) * K_pre ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i + half ) * K_pre ) + j )) ”
.

Definition build_safety_wit_19 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (((i + half ) * K_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i + half ) * K_pre )) ”
.

Definition build_safety_wit_20 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((i + half ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + half )) ”
.

Definition build_safety_wit_21 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition build_safety_wit_22 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (((i * K_pre ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * K_pre ) + j )) ”
.

Definition build_safety_wit_23 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i * K_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * K_pre )) ”
.

Definition build_safety_wit_24 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (((i * K_pre ) + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * K_pre ) + j )) ”
.

Definition build_safety_wit_25 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i * K_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * K_pre )) ”
.

Definition build_safety_wit_26 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH16 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH17 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH18 : (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) )) (PreH19 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH16 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH17 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH18 : (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) )) (PreH19 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition build_safety_wit_26_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH16 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH17 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH18 : (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) )) (PreH19 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition build_safety_wit_26_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH16 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH17 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH18 : (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) )) (PreH19 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> half)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition build_safety_wit_27 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> len)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((len * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len * 2 )) ”
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> len)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((len * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len * 2 )) ”
).

Definition build_safety_wit_27_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> len)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((len * 2 ) <= INT_MAX) ”
.

Definition build_safety_wit_27_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> len)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= (len * 2 )) ”
.

Definition build_safety_wit_28 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> len)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition build_safety_wit_29 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "half" ) )) # Int  |-> len)
  **  ((( &( "len" ) )) # Int  |-> (len * 2 ))
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition build_entail_wit_1 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st0)) = (n_pre * K_pre ))) (PreH9 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st0 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre * K_pre )) ” 
  &&  “ (STZeroPrefix st_l 0 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st0)) = (n_pre * K_pre ))) (PreH9 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STZeroPrefix st0 0 ) ”
  &&  emp
).

Definition build_entail_wit_1_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st0)) = (n_pre * K_pre ))) (PreH9 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> ((INT_MIN <= (Znth idx l 0)) /\ ((Znth idx l 0) <= INT_MAX)))) ,
  (STZeroPrefix st0 0 )
.

Definition build_entail_wit_2 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l_2 idx )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth (idx) (0) (st_l_2)) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * K_pre )) ” 
  &&  “ (STZeroPrefix st_l (idx + 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l_2 idx )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STZeroPrefix (replace_Znth (idx) (0) (st_l_2)) (idx + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth (idx) (0) (st_l_2)))) = (n_pre * K_pre )) ”
  &&  emp
).

Definition build_entail_wit_2_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l_2 idx )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (STZeroPrefix (replace_Znth (idx) (0) (st_l_2)) (idx + 1 ) )
.

Definition build_entail_wit_2_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l_2 idx )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  ((Zlength ((replace_Znth (idx) (0) (st_l_2)))) = (n_pre * K_pre ))
.

Definition build_entail_wit_3 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx >= (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l_2 idx )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (STZeroPrefix st_l (n_pre * K_pre ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx >= (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l_2 idx )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STZeroPrefix st_l_2 (n_pre * K_pre ) ) ”
  &&  emp
).

Definition build_entail_wit_3_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx >= (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l_2 idx )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STZeroPrefix st_l_2 (n_pre * K_pre ) )
.

Definition build_entail_wit_4 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (STZeroPrefix st_l_2 (n_pre * K_pre ) )) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre 0 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (STZeroPrefix st_l_2 (n_pre * K_pre ) )) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STBasePrefix l st_l_2 K_pre n_pre 0 ) ”
  &&  emp
).

Definition build_entail_wit_4_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (STZeroPrefix st_l_2 (n_pre * K_pre ) )) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STBasePrefix l st_l_2 K_pre n_pre 0 )
.

Definition build_entail_wit_5 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (i * K_pre )) ” 
  &&  “ ((i * K_pre ) < (n_pre * K_pre )) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre i ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((i * K_pre ) < (n_pre * K_pre )) ”
  &&  emp
).

Definition build_entail_wit_5_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  ((i * K_pre ) < (n_pre * K_pre ))
.

Definition build_entail_wit_6 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= (i * K_pre ))) (PreH12 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH13 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre (i + 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= (i * K_pre ))) (PreH12 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH13 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STBasePrefix l (replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)) K_pre n_pre (i + 1 ) ) ” 
  &&  “ ((Zlength ((replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)))) = (n_pre * K_pre )) ”
  &&  emp
).

Definition build_entail_wit_6_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= (i * K_pre ))) (PreH12 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH13 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STBasePrefix l (replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)) K_pre n_pre (i + 1 ) )
.

Definition build_entail_wit_6_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= (i * K_pre ))) (PreH12 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH13 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  ((Zlength ((replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)))) = (n_pre * K_pre ))
.

Definition build_entail_wit_7 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (STBasePrefix l st_l_2 K_pre n_pre (i + 1 ) )) (PreH12 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre (i + 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition build_entail_wit_8 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre 1 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 ) ”
  &&  emp
).

Definition build_entail_wit_8_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (0 <= i)) (PreH11 : (i <= n_pre)) (PreH12 : (STBasePrefix l st_l_2 K_pre n_pre i )) (PreH13 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )
.

Definition build_entail_wit_9 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (1 = (Power2 ((1 - 1 )))) ” 
  &&  “ (2 = (Power2 (1))) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre 1 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (2 = (Power2 (1))) ” 
  &&  “ (1 = (Power2 ((1 - 1 )))) ”
  &&  emp
).

Definition build_entail_wit_9_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (2 = (Power2 (1)))
.

Definition build_entail_wit_9_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )) (PreH10 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (1 = (Power2 ((1 - 1 ))))
.

Definition build_entail_wit_10 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j < K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j <= K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH15 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j 0 ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j < K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j <= K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH15 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STLevelPrefix l st_l_2 K_pre n_pre j 0 ) ”
  &&  emp
).

Definition build_entail_wit_10_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j < K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j <= K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH15 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STLevelPrefix l st_l_2 K_pre n_pre j 0 )
.

Definition build_entail_wit_11 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (0 <= (((i * K_pre ) + j ) - 1 )) ” 
  &&  “ ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((i + half ) * K_pre ) + j ) - 1 )) ” 
  &&  “ (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((i * K_pre ) + j )) ” 
  &&  “ (((i * K_pre ) + j ) < (n_pre * K_pre )) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l_2 K_pre i (j - 1 ) ) ” 
  &&  “ (((i * K_pre ) + j ) < (n_pre * K_pre )) ” 
  &&  “ (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((i + half ) * K_pre ) + j ) - 1 )) ” 
  &&  “ ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ”
  &&  emp
).

Definition build_entail_wit_11_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )
.

Definition build_entail_wit_11_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )
.

Definition build_entail_wit_11_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (((i * K_pre ) + j ) < (n_pre * K_pre ))
.

Definition build_entail_wit_11_split_goal_4 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))
.

Definition build_entail_wit_11_split_goal_5 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))
.

Definition build_entail_wit_11_split_goal_6 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))
.

Definition build_entail_wit_12 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l_2: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l_2)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (0 <= (((i * K_pre ) + j ) - 1 )) ” 
  &&  “ ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((i + half ) * K_pre ) + j ) - 1 )) ” 
  &&  “ (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((i * K_pre ) + j )) ” 
  &&  “ (((i * K_pre ) + j ) < (n_pre * K_pre )) ” 
  &&  “ ((Znth (((i * K_pre ) + j ) - 1 ) st_l 0) = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0)) ” 
  &&  “ ((Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0) = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0)) ” 
  &&  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l_2 K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l_2 K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
.

Definition build_entail_wit_13_1 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STLevelPrefix l (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre j (i + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevel l (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre j ) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) 0)) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) 0)) ” 
  &&  “ ((Zlength ((replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)))) = (n_pre * K_pre )) ”
  &&  emp
).

Definition build_entail_wit_13_1_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STLevelPrefix l (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre j (i + 1 ) )
.

Definition build_entail_wit_13_1_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STBuiltBeforeLevel l (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre j )
.

Definition build_entail_wit_13_1_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) 0))
.

Definition build_entail_wit_13_1_split_goal_4 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (a = (Znth (((i * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) 0))
.

Definition build_entail_wit_13_1_split_goal_5 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  ((Zlength ((replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)))) = (n_pre * K_pre ))
.

Definition build_entail_wit_13_2 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STLevelPrefix l (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre j (i + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevel l (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre j ) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) 0)) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) 0)) ” 
  &&  “ ((Zlength ((replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)))) = (n_pre * K_pre )) ”
  &&  emp
).

Definition build_entail_wit_13_2_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STLevelPrefix l (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre j (i + 1 ) )
.

Definition build_entail_wit_13_2_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STBuiltBeforeLevel l (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre j )
.

Definition build_entail_wit_13_2_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) 0))
.

Definition build_entail_wit_13_2_split_goal_4 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (a = (Znth (((i * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) 0))
.

Definition build_entail_wit_13_2_split_goal_5 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  ((Zlength ((replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)))) = (n_pre * K_pre ))
.

Definition build_entail_wit_14 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH16 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH17 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH18 : (STLevelPrefix l st_l_2 K_pre n_pre j (i + 1 ) )) (PreH19 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH16 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH17 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH18 : (STLevelPrefix l st_l_2 K_pre n_pre j (i + 1 ) )) (PreH19 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((i + 1 ) <= n_pre) ”
  &&  emp
).

Definition build_entail_wit_14_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH16 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH17 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH18 : (STLevelPrefix l st_l_2 K_pre n_pre j (i + 1 ) )) (PreH19 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  ((i + 1 ) <= n_pre)
.

Definition build_entail_wit_15 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) ) ”
  &&  emp
).

Definition build_entail_wit_15_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : (i <= n_pre)) (PreH16 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH17 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH18 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )
.

Definition build_entail_wit_16 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= K_pre) ” 
  &&  “ (len = (Power2 (((j + 1 ) - 1 )))) ” 
  &&  “ ((len * 2 ) = (Power2 ((j + 1 )))) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ ((len * 2 ) = (Power2 ((j + 1 )))) ” 
  &&  “ (len = (Power2 (((j + 1 ) - 1 )))) ”
  &&  emp
).

Definition build_entail_wit_16_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  ((len * 2 ) = (Power2 ((j + 1 ))))
.

Definition build_entail_wit_16_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )) (PreH14 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < n_pre)) -> ((INT_MIN <= (Znth p_2 l 0)) /\ ((Znth p_2 l 0) <= INT_MAX)))) ,
  (len = (Power2 (((j + 1 ) - 1 ))))
.

Definition build_return_wit_1 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j >= K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j <= K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j >= K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j <= K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (STBuilt l st_l_2 K_pre n_pre ) ”
  &&  emp
).

Definition build_return_wit_1_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j >= K_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l_2)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j <= K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH15 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (STBuilt l st_l_2 K_pre n_pre )
.

Definition build_partial_solve_wit_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (0 <= idx)) (PreH11 : (idx <= (n_pre * K_pre ))) (PreH12 : (STZeroPrefix st_l idx )) (PreH13 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (idx < (n_pre * K_pre )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * K_pre )) ” 
  &&  “ (STZeroPrefix st_l idx ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (((st_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre idx 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= (i * K_pre ))) (PreH12 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH13 : (STBasePrefix l st_l K_pre n_pre i )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (i * K_pre )) ” 
  &&  “ ((i * K_pre ) < (n_pre * K_pre )) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre i ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition build_partial_solve_wit_3 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (0 <= i)) (PreH10 : (i < n_pre)) (PreH11 : (0 <= (i * K_pre ))) (PreH12 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH13 : (STBasePrefix l st_l K_pre n_pre i )) (PreH14 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (i * K_pre )) ” 
  &&  “ ((i * K_pre ) < (n_pre * K_pre )) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre i ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (((st_pre + ((i * K_pre ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre (i * K_pre ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_4 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (0 <= (((i * K_pre ) + j ) - 1 )) ” 
  &&  “ ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((i + half ) * K_pre ) + j ) - 1 )) ” 
  &&  “ (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((i * K_pre ) + j )) ” 
  &&  “ (((i * K_pre ) + j ) < (n_pre * K_pre )) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (((st_pre + ((((i * K_pre ) + j ) - 1 ) * sizeof(INT)))) # Int  |-> (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))
  **  (IntArray.missing_i st_pre (((i * K_pre ) + j ) - 1 ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_5 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : ((Zlength (l)) = n_pre)) (PreH8 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH9 : (1 <= j)) (PreH10 : (j < K_pre)) (PreH11 : (half = (Power2 ((j - 1 ))))) (PreH12 : (len = (Power2 (j)))) (PreH13 : (0 <= i)) (PreH14 : ((i + len ) <= n_pre)) (PreH15 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH16 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH18 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH19 : (0 <= ((i * K_pre ) + j ))) (PreH20 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (0 <= (((i * K_pre ) + j ) - 1 )) ” 
  &&  “ ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((i + half ) * K_pre ) + j ) - 1 )) ” 
  &&  “ (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((i * K_pre ) + j )) ” 
  &&  “ (((i * K_pre ) + j ) < (n_pre * K_pre )) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (((st_pre + (((((i + half ) * K_pre ) + j ) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))
  **  (IntArray.missing_i st_pre ((((i + half ) * K_pre ) + j ) - 1 ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_6 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (a >= b) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (0 <= (((i * K_pre ) + j ) - 1 )) ” 
  &&  “ ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((i + half ) * K_pre ) + j ) - 1 )) ” 
  &&  “ (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((i * K_pre ) + j )) ” 
  &&  “ (((i * K_pre ) + j ) < (n_pre * K_pre )) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (((st_pre + (((i * K_pre ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre ((i * K_pre ) + j ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_7 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : ((Zlength (l)) = n_pre)) (PreH9 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH10 : (1 <= j)) (PreH11 : (j < K_pre)) (PreH12 : (half = (Power2 ((j - 1 ))))) (PreH13 : (len = (Power2 (j)))) (PreH14 : (0 <= i)) (PreH15 : ((i + len ) <= n_pre)) (PreH16 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH17 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH18 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH19 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH20 : (0 <= ((i * K_pre ) + j ))) (PreH21 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH22 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH23 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) (PreH28 : forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX)))) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (a < b) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (0 <= (((i * K_pre ) + j ) - 1 )) ” 
  &&  “ ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((i + half ) * K_pre ) + j ) - 1 )) ” 
  &&  “ (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((i * K_pre ) + j )) ” 
  &&  “ (((i * K_pre ) + j ) < (n_pre * K_pre )) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < n_pre)) -> ((INT_MIN <= (Znth p l 0)) /\ ((Znth p l 0) <= INT_MAX))) ”
  &&  (((st_pre + (((i * K_pre ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre ((i * K_pre ) + j ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

(*----- Function query -----*)

Definition query_safety_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH12 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (((right_pre - left_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right_pre - left_pre ) + 1 )) ”
.

Definition query_safety_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH12 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((right_pre - left_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right_pre - left_pre )) ”
.

Definition query_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH12 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH12 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> ((right_pre - left_pre ) + 1 ))
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition query_safety_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH12 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "pow" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> ((right_pre - left_pre ) + 1 ))
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_6 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((pow * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pow * 2 )) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((pow * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pow * 2 )) ”
).

Definition query_safety_wit_6_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((pow * 2 ) <= INT_MAX) ”
.

Definition query_safety_wit_6_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= (pow * 2 )) ”
.

Definition query_safety_wit_7 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_8 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((pow * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pow * 2 )) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((pow * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pow * 2 )) ”
).

Definition query_safety_wit_8_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((pow * 2 ) <= INT_MAX) ”
.

Definition query_safety_wit_8_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= (pow * 2 )) ”
.

Definition query_safety_wit_9 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition query_safety_wit_10 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> (pow * 2 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> (pow * 2 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
).

Definition query_safety_wit_10_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> (pow * 2 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((k + 1 ) <= INT_MAX) ”
.

Definition query_safety_wit_10_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> (pow * 2 ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition query_safety_wit_11 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (((left_pre * K_pre ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((left_pre * K_pre ) + k )) ”
.

Definition query_safety_wit_12 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((left_pre * K_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_pre * K_pre )) ”
.

Definition query_safety_wit_13 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((left_pre * K_pre ) + k ) st_l 0))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((((right_pre - pow ) + 1 ) * K_pre ) + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ”
.

Definition query_safety_wit_14 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((left_pre * K_pre ) + k ) st_l 0))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((((right_pre - pow ) + 1 ) * K_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((right_pre - pow ) + 1 ) * K_pre )) ”
.

Definition query_safety_wit_15 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((left_pre * K_pre ) + k ) st_l 0))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (((right_pre - pow ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right_pre - pow ) + 1 )) ”
.

Definition query_safety_wit_16 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((left_pre * K_pre ) + k ) st_l 0))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ ((right_pre - pow ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right_pre - pow )) ”
.

Definition query_safety_wit_17 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  ((( &( "b" ) )) # Int  |->_)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  ((( &( "a" ) )) # Int  |-> (Znth ((left_pre * K_pre ) + k ) st_l 0))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "pow" ) )) # Int  |-> pow)
  **  ((( &( "k" ) )) # Int  |-> k)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_entail_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH12 : (STBuilt l st_l K_pre n_pre )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (((right_pre - left_pre ) + 1 ) = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogLoopState K_pre n_pre ((right_pre - left_pre ) + 1 ) 0 1 ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH12 : (STBuilt l st_l K_pre n_pre )) ,
  TT && emp 
|--
  “ (QueryLogLoopState K_pre n_pre ((right_pre - left_pre ) + 1 ) 0 1 ) ”
  &&  emp
).

Definition query_entail_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : ((Zlength (l)) = n_pre)) (PreH11 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH12 : (STBuilt l st_l K_pre n_pre )) ,
  (QueryLogLoopState K_pre n_pre ((right_pre - left_pre ) + 1 ) 0 1 )
.

Definition query_entail_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogLoopState K_pre n_pre len (k + 1 ) (pow * 2 ) ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  TT && emp 
|--
  “ (QueryLogLoopState K_pre n_pre len (k + 1 ) (pow * 2 ) ) ”
  &&  emp
).

Definition query_entail_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (QueryLogLoopState K_pre n_pre len (k + 1 ) (pow * 2 ) )
.

Definition query_entail_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogFinalState K_pre n_pre len k pow ) ” 
  &&  “ (0 <= ((left_pre * K_pre ) + k )) ” 
  &&  “ (((left_pre * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ” 
  &&  “ (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (STCellRangeMax l st_l K_pre left_pre k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  TT && emp 
|--
  “ (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre left_pre k ) ” 
  &&  “ (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ” 
  &&  “ (((left_pre * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((left_pre * K_pre ) + k )) ” 
  &&  “ (QueryLogFinalState K_pre n_pre len k pow ) ”
  &&  emp
).

Definition query_entail_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )
.

Definition query_entail_wit_3_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (STCellRangeMax l st_l K_pre left_pre k )
.

Definition query_entail_wit_3_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))
.

Definition query_entail_wit_3_split_goal_4 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))
.

Definition query_entail_wit_3_split_goal_5 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))
.

Definition query_entail_wit_3_split_goal_6 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (0 <= ((left_pre * K_pre ) + k ))
.

Definition query_entail_wit_3_split_goal_7 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (STBuilt l st_l K_pre n_pre )) (PreH15 : (QueryLogLoopState K_pre n_pre len k pow )) ,
  (QueryLogFinalState K_pre n_pre len k pow )
.

Definition query_entail_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ ((Znth ((left_pre * K_pre ) + k ) st_l 0) = (Znth ((left_pre * K_pre ) + k ) st_l 0)) ” 
  &&  “ ((Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0) = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0)) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogFinalState K_pre n_pre len k pow ) ” 
  &&  “ (STCellRangeMax l st_l K_pre left_pre k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition query_entail_wit_5 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH15 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH16 : (STBuilt l st_l K_pre n_pre )) (PreH17 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH18 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH19 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (a = (Znth ((left_pre * K_pre ) + k ) st_l 0)) ” 
  &&  “ (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0)) ” 
  &&  “ (QueryLogFinalState K_pre n_pre len k pow ) ” 
  &&  “ (RangeMaxValue l left_pre (right_pre + 1 ) a ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH15 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH16 : (STBuilt l st_l K_pre n_pre )) (PreH17 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH18 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH19 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  TT && emp 
|--
  “ (RangeMaxValue l left_pre (right_pre + 1 ) a ) ”
  &&  emp
).

Definition query_entail_wit_5_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a >= b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH15 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH16 : (STBuilt l st_l K_pre n_pre )) (PreH17 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH18 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH19 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (RangeMaxValue l left_pre (right_pre + 1 ) a )
.

Definition query_entail_wit_6 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH15 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH16 : (STBuilt l st_l K_pre n_pre )) (PreH17 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH18 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH19 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (a = (Znth ((left_pre * K_pre ) + k ) st_l 0)) ” 
  &&  “ (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0)) ” 
  &&  “ (QueryLogFinalState K_pre n_pre len k pow ) ” 
  &&  “ (RangeMaxValue l left_pre (right_pre + 1 ) b ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH15 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH16 : (STBuilt l st_l K_pre n_pre )) (PreH17 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH18 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH19 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  TT && emp 
|--
  “ (RangeMaxValue l left_pre (right_pre + 1 ) b ) ”
  &&  emp
).

Definition query_entail_wit_6_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a < b)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= K_pre)) (PreH5 : (K_pre <= 30)) (PreH6 : ((n_pre * K_pre ) <= 1000000)) (PreH7 : (n_pre < (Power2 (K_pre)))) (PreH8 : (0 <= left_pre)) (PreH9 : (left_pre <= right_pre)) (PreH10 : (right_pre < n_pre)) (PreH11 : (len = ((right_pre - left_pre ) + 1 ))) (PreH12 : ((Zlength (l)) = n_pre)) (PreH13 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH14 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH15 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH16 : (STBuilt l st_l K_pre n_pre )) (PreH17 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH18 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH19 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (RangeMaxValue l left_pre (right_pre + 1 ) b )
.

Definition query_return_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= right_pre)) (PreH7 : (right_pre < n_pre)) (PreH8 : (len = ((right_pre - left_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH11 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH12 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH13 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH14 : (RangeMaxValue l left_pre (right_pre + 1 ) b )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RangeMaxValue l left_pre (right_pre + 1 ) b ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition query_return_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : (0 <= left_pre)) (PreH6 : (left_pre <= right_pre)) (PreH7 : (right_pre < n_pre)) (PreH8 : (len = ((right_pre - left_pre ) + 1 ))) (PreH9 : ((Zlength (l)) = n_pre)) (PreH10 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH11 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH12 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH13 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH14 : (RangeMaxValue l left_pre (right_pre + 1 ) a )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RangeMaxValue l left_pre (right_pre + 1 ) a ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition query_partial_solve_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogFinalState K_pre n_pre len k pow ) ” 
  &&  “ (0 <= ((left_pre * K_pre ) + k )) ” 
  &&  “ (((left_pre * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ” 
  &&  “ (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (STCellRangeMax l st_l K_pre left_pre k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k ) ”
  &&  (((st_pre + (((left_pre * K_pre ) + k ) * sizeof(INT)))) # Int  |-> (Znth ((left_pre * K_pre ) + k ) st_l 0))
  **  (IntArray.missing_i st_pre ((left_pre * K_pre ) + k ) 0 (n_pre * K_pre ) st_l )
.

Definition query_partial_solve_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= K_pre)) (PreH4 : (K_pre <= 30)) (PreH5 : ((n_pre * K_pre ) <= 1000000)) (PreH6 : (n_pre < (Power2 (K_pre)))) (PreH7 : (0 <= left_pre)) (PreH8 : (left_pre <= right_pre)) (PreH9 : (right_pre < n_pre)) (PreH10 : (len = ((right_pre - left_pre ) + 1 ))) (PreH11 : ((Zlength (l)) = n_pre)) (PreH12 : ((Zlength (st_l)) = (n_pre * K_pre ))) (PreH13 : (STBuilt l st_l K_pre n_pre )) (PreH14 : (QueryLogFinalState K_pre n_pre len k pow )) (PreH15 : (0 <= ((left_pre * K_pre ) + k ))) (PreH16 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH17 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH18 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH19 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH20 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (K_pre <= 30) ” 
  &&  “ ((n_pre * K_pre ) <= 1000000) ” 
  &&  “ (n_pre < (Power2 (K_pre))) ” 
  &&  “ (0 <= left_pre) ” 
  &&  “ (left_pre <= right_pre) ” 
  &&  “ (right_pre < n_pre) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (st_l)) = (n_pre * K_pre )) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogFinalState K_pre n_pre len k pow ) ” 
  &&  “ (0 <= ((left_pre * K_pre ) + k )) ” 
  &&  “ (((left_pre * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ” 
  &&  “ (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (STCellRangeMax l st_l K_pre left_pre k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k ) ”
  &&  (((st_pre + (((((right_pre - pow ) + 1 ) * K_pre ) + k ) * sizeof(INT)))) # Int  |-> (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))
  **  (IntArray.missing_i st_pre ((((right_pre - pow ) + 1 ) * K_pre ) + k ) 0 (n_pre * K_pre ) st_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_build_safety_wit_1 : build_safety_wit_1.
Axiom proof_of_build_safety_wit_2 : build_safety_wit_2.
Axiom proof_of_build_safety_wit_3 : build_safety_wit_3.
Axiom proof_of_build_safety_wit_4 : build_safety_wit_4.
Axiom proof_of_build_safety_wit_5 : build_safety_wit_5.
Axiom proof_of_build_safety_wit_6 : build_safety_wit_6.
Axiom proof_of_build_safety_wit_7 : build_safety_wit_7.
Axiom proof_of_build_safety_wit_8 : build_safety_wit_8.
Axiom proof_of_build_safety_wit_9 : build_safety_wit_9.
Axiom proof_of_build_safety_wit_10 : build_safety_wit_10.
Axiom proof_of_build_safety_wit_11 : build_safety_wit_11.
Axiom proof_of_build_safety_wit_12 : build_safety_wit_12.
Axiom proof_of_build_safety_wit_13 : build_safety_wit_13.
Axiom proof_of_build_safety_wit_14 : build_safety_wit_14.
Axiom proof_of_build_safety_wit_15 : build_safety_wit_15.
Axiom proof_of_build_safety_wit_16 : build_safety_wit_16.
Axiom proof_of_build_safety_wit_17 : build_safety_wit_17.
Axiom proof_of_build_safety_wit_18 : build_safety_wit_18.
Axiom proof_of_build_safety_wit_19 : build_safety_wit_19.
Axiom proof_of_build_safety_wit_20 : build_safety_wit_20.
Axiom proof_of_build_safety_wit_21 : build_safety_wit_21.
Axiom proof_of_build_safety_wit_22 : build_safety_wit_22.
Axiom proof_of_build_safety_wit_23 : build_safety_wit_23.
Axiom proof_of_build_safety_wit_24 : build_safety_wit_24.
Axiom proof_of_build_safety_wit_25 : build_safety_wit_25.
Axiom proof_of_build_safety_wit_26 : build_safety_wit_26.
Axiom proof_of_build_safety_wit_27 : build_safety_wit_27.
Axiom proof_of_build_safety_wit_28 : build_safety_wit_28.
Axiom proof_of_build_safety_wit_29 : build_safety_wit_29.
Axiom proof_of_build_entail_wit_1 : build_entail_wit_1.
Axiom proof_of_build_entail_wit_2 : build_entail_wit_2.
Axiom proof_of_build_entail_wit_3 : build_entail_wit_3.
Axiom proof_of_build_entail_wit_4 : build_entail_wit_4.
Axiom proof_of_build_entail_wit_5 : build_entail_wit_5.
Axiom proof_of_build_entail_wit_6 : build_entail_wit_6.
Axiom proof_of_build_entail_wit_7 : build_entail_wit_7.
Axiom proof_of_build_entail_wit_8 : build_entail_wit_8.
Axiom proof_of_build_entail_wit_9 : build_entail_wit_9.
Axiom proof_of_build_entail_wit_10 : build_entail_wit_10.
Axiom proof_of_build_entail_wit_11 : build_entail_wit_11.
Axiom proof_of_build_entail_wit_12 : build_entail_wit_12.
Axiom proof_of_build_entail_wit_13_1 : build_entail_wit_13_1.
Axiom proof_of_build_entail_wit_13_2 : build_entail_wit_13_2.
Axiom proof_of_build_entail_wit_14 : build_entail_wit_14.
Axiom proof_of_build_entail_wit_15 : build_entail_wit_15.
Axiom proof_of_build_entail_wit_16 : build_entail_wit_16.
Axiom proof_of_build_return_wit_1 : build_return_wit_1.
Axiom proof_of_build_partial_solve_wit_1 : build_partial_solve_wit_1.
Axiom proof_of_build_partial_solve_wit_2 : build_partial_solve_wit_2.
Axiom proof_of_build_partial_solve_wit_3 : build_partial_solve_wit_3.
Axiom proof_of_build_partial_solve_wit_4 : build_partial_solve_wit_4.
Axiom proof_of_build_partial_solve_wit_5 : build_partial_solve_wit_5.
Axiom proof_of_build_partial_solve_wit_6 : build_partial_solve_wit_6.
Axiom proof_of_build_partial_solve_wit_7 : build_partial_solve_wit_7.
Axiom proof_of_query_safety_wit_1 : query_safety_wit_1.
Axiom proof_of_query_safety_wit_2 : query_safety_wit_2.
Axiom proof_of_query_safety_wit_3 : query_safety_wit_3.
Axiom proof_of_query_safety_wit_4 : query_safety_wit_4.
Axiom proof_of_query_safety_wit_5 : query_safety_wit_5.
Axiom proof_of_query_safety_wit_6 : query_safety_wit_6.
Axiom proof_of_query_safety_wit_7 : query_safety_wit_7.
Axiom proof_of_query_safety_wit_8 : query_safety_wit_8.
Axiom proof_of_query_safety_wit_9 : query_safety_wit_9.
Axiom proof_of_query_safety_wit_10 : query_safety_wit_10.
Axiom proof_of_query_safety_wit_11 : query_safety_wit_11.
Axiom proof_of_query_safety_wit_12 : query_safety_wit_12.
Axiom proof_of_query_safety_wit_13 : query_safety_wit_13.
Axiom proof_of_query_safety_wit_14 : query_safety_wit_14.
Axiom proof_of_query_safety_wit_15 : query_safety_wit_15.
Axiom proof_of_query_safety_wit_16 : query_safety_wit_16.
Axiom proof_of_query_safety_wit_17 : query_safety_wit_17.
Axiom proof_of_query_entail_wit_1 : query_entail_wit_1.
Axiom proof_of_query_entail_wit_2 : query_entail_wit_2.
Axiom proof_of_query_entail_wit_3 : query_entail_wit_3.
Axiom proof_of_query_entail_wit_4 : query_entail_wit_4.
Axiom proof_of_query_entail_wit_5 : query_entail_wit_5.
Axiom proof_of_query_entail_wit_6 : query_entail_wit_6.
Axiom proof_of_query_return_wit_1 : query_return_wit_1.
Axiom proof_of_query_return_wit_2 : query_return_wit_2.
Axiom proof_of_query_partial_solve_wit_1 : query_partial_solve_wit_1.
Axiom proof_of_query_partial_solve_wit_2 : query_partial_solve_wit_2.

End VC_Correct.
