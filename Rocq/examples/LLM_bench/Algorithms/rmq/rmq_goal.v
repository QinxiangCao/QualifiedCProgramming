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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st0 K_pre n_pre )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition build_safety_wit_2 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= idx)) (PreH5 : (idx <= (n_pre * K_pre ))) (PreH6 : (STZeroPrefixBounds st_l idx )) (PreH7 : (STZeroPrefix st_l idx )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= idx)) (PreH5 : (idx <= (n_pre * K_pre ))) (PreH6 : (STZeroPrefixBounds st_l idx )) (PreH7 : (STZeroPrefix st_l idx )) ,
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
).

Definition build_safety_wit_2_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= idx)) (PreH5 : (idx <= (n_pre * K_pre ))) (PreH6 : (STZeroPrefixBounds st_l idx )) (PreH7 : (STZeroPrefix st_l idx )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((n_pre * K_pre ) <= INT_MAX) ”
.

Definition build_safety_wit_2_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= idx)) (PreH5 : (idx <= (n_pre * K_pre ))) (PreH6 : (STZeroPrefixBounds st_l idx )) (PreH7 : (STZeroPrefix st_l idx )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= (n_pre * K_pre )) ”
.

Definition build_safety_wit_3 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l idx )) (PreH8 : (STZeroPrefix st_l idx )) ,
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
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l idx )) (PreH8 : (STZeroPrefix st_l idx )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l idx )) (PreH8 : (STZeroPrefix st_l idx )) ,
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
).

Definition build_safety_wit_4_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l idx )) (PreH8 : (STZeroPrefix st_l idx )) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth (idx) (0) (st_l)) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((idx + 1 ) <= INT_MAX) ”
.

Definition build_safety_wit_4_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l idx )) (PreH8 : (STZeroPrefix st_l idx )) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth (idx) (0) (st_l)) )
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  (IntArray.full arr_pre n_pre l )
|--
  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition build_safety_wit_5 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (STZeroPrefixBounds st_l (n_pre * K_pre ) )) (PreH5 : (STZeroPrefix st_l (n_pre * K_pre ) )) ,
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
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l K_pre i 0 )) (PreH10 : (STBasePrefix l st_l K_pre n_pre i )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l K_pre i 0 )) (PreH10 : (STBasePrefix l st_l K_pre n_pre i )) ,
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
).

Definition build_safety_wit_6_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l K_pre i 0 )) (PreH10 : (STBasePrefix l st_l K_pre n_pre i )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((i * K_pre ) <= INT_MAX) ”
.

Definition build_safety_wit_6_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l K_pre i 0 )) (PreH10 : (STBasePrefix l st_l K_pre n_pre i )) ,
  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= (i * K_pre )) ”
.

Definition build_safety_wit_7 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (STBasePrefixBounds n_pre (i + 1 ) )) (PreH7 : (STBasePrefix l st_l K_pre n_pre (i + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1 )) (PreH5 : (STBuiltBeforeLevel l st_l K_pre n_pre 1 )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1 )) (PreH5 : (STBuiltBeforeLevel l st_l K_pre n_pre 1 )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1 )) (PreH5 : (STBuiltBeforeLevel l st_l K_pre n_pre 1 )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre j )) (PreH9 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH11 : (STLevelPrefix l st_l K_pre n_pre j i )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre j )) (PreH9 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH11 : (STLevelPrefix l st_l K_pre n_pre j i )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre j )) (PreH9 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH11 : (STLevelPrefix l st_l K_pre n_pre j i )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre j )) (PreH9 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH10 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH11 : (STLevelPrefix l st_l K_pre n_pre j i )) ,
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
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_13_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_13_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= (((i * K_pre ) + j ) - 1 )) ”
.

Definition build_safety_wit_14 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_14_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_14_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= ((i * K_pre ) + j )) ”
.

Definition build_safety_wit_15 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_15_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_15_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= (i * K_pre )) ”
.

Definition build_safety_wit_16 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_17_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_17_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= ((((i + half ) * K_pre ) + j ) - 1 )) ”
.

Definition build_safety_wit_18 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_18_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_18_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= (((i + half ) * K_pre ) + j )) ”
.

Definition build_safety_wit_19 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_19_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_19_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= ((i + half ) * K_pre )) ”
.

Definition build_safety_wit_20 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_20_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_20_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= (i + half )) ”
.

Definition build_safety_wit_21 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_22_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_22_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= ((i * K_pre ) + j )) ”
.

Definition build_safety_wit_23 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_23_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_23_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= (i * K_pre )) ”
.

Definition build_safety_wit_24 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_24_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_24_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= ((i * K_pre ) + j )) ”
.

Definition build_safety_wit_25 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
) \/
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
).

Definition build_safety_wit_25_split_goal_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
.

Definition build_safety_wit_25_split_goal_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
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
  “ ((INT_MIN) <= (i * K_pre )) ”
.

Definition build_safety_wit_26 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH11 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j )) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1 ) )) (PreH14 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH15 : (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH11 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j )) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1 ) )) (PreH14 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH15 : (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH11 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j )) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1 ) )) (PreH14 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH15 : (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH11 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j )) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1 ) )) (PreH14 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH15 : (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) )) ,
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
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st0 K_pre n_pre )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st0 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n_pre * K_pre )) ” 
  &&  “ (STZeroPrefixBounds st_l 0 ) ” 
  &&  “ (STZeroPrefix st_l 0 ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st0 K_pre n_pre )) ,
  TT && emp 
|--
  “ (STZeroPrefix st0 0 ) ” 
  &&  “ (STZeroPrefixBounds st0 0 ) ” 
  &&  “ (0 <= (n_pre * K_pre )) ”
  &&  emp
).

Definition build_entail_wit_1_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st0 K_pre n_pre )) ,
  (STZeroPrefix st0 0 )
.

Definition build_entail_wit_1_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st0 K_pre n_pre )) ,
  (STZeroPrefixBounds st0 0 )
.

Definition build_entail_wit_1_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (st0: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st0 K_pre n_pre )) ,
  (0 <= (n_pre * K_pre ))
.

Definition build_entail_wit_2 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l_2 idx )) (PreH8 : (STZeroPrefix st_l_2 idx )) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth (idx) (0) (st_l_2)) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= (n_pre * K_pre )) ” 
  &&  “ (STZeroPrefixBounds st_l (idx + 1 ) ) ” 
  &&  “ (STZeroPrefix st_l (idx + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l_2 idx )) (PreH8 : (STZeroPrefix st_l_2 idx )) ,
  TT && emp 
|--
  “ (STZeroPrefix (replace_Znth (idx) (0) (st_l_2)) (idx + 1 ) ) ” 
  &&  “ (STZeroPrefixBounds (replace_Znth (idx) (0) (st_l_2)) (idx + 1 ) ) ” 
  &&  “ (STTableShape (replace_Znth (idx) (0) (st_l_2)) K_pre n_pre ) ”
  &&  emp
).

Definition build_entail_wit_2_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l_2 idx )) (PreH8 : (STZeroPrefix st_l_2 idx )) ,
  (STZeroPrefix (replace_Znth (idx) (0) (st_l_2)) (idx + 1 ) )
.

Definition build_entail_wit_2_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l_2 idx )) (PreH8 : (STZeroPrefix st_l_2 idx )) ,
  (STZeroPrefixBounds (replace_Znth (idx) (0) (st_l_2)) (idx + 1 ) )
.

Definition build_entail_wit_2_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l_2 idx )) (PreH8 : (STZeroPrefix st_l_2 idx )) ,
  (STTableShape (replace_Znth (idx) (0) (st_l_2)) K_pre n_pre )
.

Definition build_entail_wit_3 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx >= (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l_2 idx )) (PreH8 : (STZeroPrefix st_l_2 idx )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STZeroPrefixBounds st_l (n_pre * K_pre ) ) ” 
  &&  “ (STZeroPrefix st_l (n_pre * K_pre ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx >= (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l_2 idx )) (PreH8 : (STZeroPrefix st_l_2 idx )) ,
  TT && emp 
|--
  “ (STZeroPrefix st_l_2 (n_pre * K_pre ) ) ” 
  &&  “ (STZeroPrefixBounds st_l_2 (n_pre * K_pre ) ) ”
  &&  emp
).

Definition build_entail_wit_3_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx >= (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l_2 idx )) (PreH8 : (STZeroPrefix st_l_2 idx )) ,
  (STZeroPrefix st_l_2 (n_pre * K_pre ) )
.

Definition build_entail_wit_3_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (st_l_2: (@list Z)) (PreH1 : (idx >= (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l_2 idx )) (PreH8 : (STZeroPrefix st_l_2 idx )) ,
  (STZeroPrefixBounds st_l_2 (n_pre * K_pre ) )
.

Definition build_entail_wit_4 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (STZeroPrefixBounds st_l_2 (n_pre * K_pre ) )) (PreH5 : (STZeroPrefix st_l_2 (n_pre * K_pre ) )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STBasePrefixBounds n_pre 0 ) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre 0 ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (STZeroPrefixBounds st_l_2 (n_pre * K_pre ) )) (PreH5 : (STZeroPrefix st_l_2 (n_pre * K_pre ) )) ,
  TT && emp 
|--
  “ (STBasePrefix l st_l_2 K_pre n_pre 0 ) ” 
  &&  “ (STBasePrefixBounds n_pre 0 ) ”
  &&  emp
).

Definition build_entail_wit_4_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (STZeroPrefixBounds st_l_2 (n_pre * K_pre ) )) (PreH5 : (STZeroPrefix st_l_2 (n_pre * K_pre ) )) ,
  (STBasePrefix l st_l_2 K_pre n_pre 0 )
.

Definition build_entail_wit_4_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (STZeroPrefixBounds st_l_2 (n_pre * K_pre ) )) (PreH5 : (STZeroPrefix st_l_2 (n_pre * K_pre ) )) ,
  (STBasePrefixBounds n_pre 0 )
.

Definition build_entail_wit_5 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (i * K_pre )) ” 
  &&  “ ((i * K_pre ) < (n_pre * K_pre )) ” 
  &&  “ (STBasePrefixBounds n_pre i ) ” 
  &&  “ (STCellBounds st_l K_pre i 0 ) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre i ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  TT && emp 
|--
  “ (STCellBounds st_l_2 K_pre i 0 ) ” 
  &&  “ ((i * K_pre ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= (i * K_pre )) ” 
  &&  “ (0 <= i) ”
  &&  emp
).

Definition build_entail_wit_5_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (STCellBounds st_l_2 K_pre i 0 )
.

Definition build_entail_wit_5_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  ((i * K_pre ) < (n_pre * K_pre ))
.

Definition build_entail_wit_5_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (0 <= (i * K_pre ))
.

Definition build_entail_wit_5_split_goal_4 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (0 <= i)
.

Definition build_entail_wit_6 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l_2 K_pre i 0 )) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (STBasePrefixBounds n_pre (i + 1 ) ) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre (i + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l_2 K_pre i 0 )) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  TT && emp 
|--
  “ (STBasePrefix l (replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)) K_pre n_pre (i + 1 ) ) ” 
  &&  “ (STBasePrefixBounds n_pre (i + 1 ) ) ” 
  &&  “ (STTableShape (replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)) K_pre n_pre ) ”
  &&  emp
).

Definition build_entail_wit_6_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l_2 K_pre i 0 )) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (STBasePrefix l (replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)) K_pre n_pre (i + 1 ) )
.

Definition build_entail_wit_6_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l_2 K_pre i 0 )) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (STBasePrefixBounds n_pre (i + 1 ) )
.

Definition build_entail_wit_6_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l_2 K_pre i 0 )) (PreH10 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (STTableShape (replace_Znth ((i * K_pre )) ((Znth i l 0)) (st_l_2)) K_pre n_pre )
.

Definition build_entail_wit_7 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (STBasePrefixBounds n_pre (i + 1 ) )) (PreH7 : (STBasePrefix l st_l_2 K_pre n_pre (i + 1 ) )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STBasePrefixBounds n_pre (i + 1 ) ) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre (i + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition build_entail_wit_8 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre 1 ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre 1 ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  TT && emp 
|--
  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre 1 ) ”
  &&  emp
).

Definition build_entail_wit_8_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )
.

Definition build_entail_wit_8_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (st_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (STBasePrefixBounds n_pre i )) (PreH6 : (STBasePrefix l st_l_2 K_pre n_pre i )) ,
  (STBuiltBeforeLevelBounds K_pre 1 )
.

Definition build_entail_wit_9 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1 )) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= K_pre) ” 
  &&  “ (1 = (Power2 ((1 - 1 )))) ” 
  &&  “ (2 = (Power2 (1))) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre 1 ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre 1 ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1 )) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )) ,
  TT && emp 
|--
  “ (2 = (Power2 (1))) ” 
  &&  “ (1 = (Power2 ((1 - 1 )))) ” 
  &&  “ (1 <= K_pre) ”
  &&  emp
).

Definition build_entail_wit_9_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1 )) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )) ,
  (2 = (Power2 (1)))
.

Definition build_entail_wit_9_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1 )) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )) ,
  (1 = (Power2 ((1 - 1 ))))
.

Definition build_entail_wit_9_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (STBuiltBeforeLevelBounds K_pre 1 )) (PreH5 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre 1 )) ,
  (1 <= K_pre)
.

Definition build_entail_wit_10 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j 0 ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j 0 ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) ,
  TT && emp 
|--
  “ (STLevelPrefix l st_l_2 K_pre n_pre j 0 ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j 0 ) ”
  &&  emp
).

Definition build_entail_wit_10_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) ,
  (STLevelPrefix l st_l_2 K_pre n_pre j 0 )
.

Definition build_entail_wit_10_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j < K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) ,
  (STLevelPrefixBounds K_pre n_pre j 0 )
.

Definition build_entail_wit_11 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
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
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j i ) ” 
  &&  “ (STCellBounds st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre i j ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  TT && emp 
|--
  “ (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l_2 K_pre i (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l_2 K_pre i j ) ” 
  &&  “ (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l_2 K_pre i (j - 1 ) ) ” 
  &&  “ (((i * K_pre ) + j ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((i * K_pre ) + j )) ” 
  &&  “ (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((i + half ) * K_pre ) + j ) - 1 )) ” 
  &&  “ ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= (((i * K_pre ) + j ) - 1 )) ” 
  &&  “ (0 <= i) ”
  &&  emp
).

Definition build_entail_wit_11_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )
.

Definition build_entail_wit_11_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )
.

Definition build_entail_wit_11_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (STCellBounds st_l_2 K_pre i j )
.

Definition build_entail_wit_11_split_goal_4 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )
.

Definition build_entail_wit_11_split_goal_5 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (STCellBounds st_l_2 K_pre i (j - 1 ) )
.

Definition build_entail_wit_11_split_goal_6 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (((i * K_pre ) + j ) < (n_pre * K_pre ))
.

Definition build_entail_wit_11_split_goal_7 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (0 <= ((i * K_pre ) + j ))
.

Definition build_entail_wit_11_split_goal_8 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))
.

Definition build_entail_wit_11_split_goal_9 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))
.

Definition build_entail_wit_11_split_goal_10 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))
.

Definition build_entail_wit_11_split_goal_11 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (0 <= (((i * K_pre ) + j ) - 1 ))
.

Definition build_entail_wit_11_split_goal_12 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) <= n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (0 <= i)
.

Definition build_entail_wit_12 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l_2: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l_2 K_pre n_pre ) ” 
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
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j i ) ” 
  &&  “ (STCellBounds st_l_2 K_pre i (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l_2 K_pre i j ) ” 
  &&  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l_2 K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l_2 K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
.

Definition build_entail_wit_13_1 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j (i + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  TT && emp 
|--
  “ (STLevelPrefix l (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre j (i + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevel l (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j (i + 1 ) ) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) 0)) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) 0)) ” 
  &&  “ (STTableShape (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre ) ”
  &&  emp
).

Definition build_entail_wit_13_1_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (STLevelPrefix l (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre j (i + 1 ) )
.

Definition build_entail_wit_13_1_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (STBuiltBeforeLevel l (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre j )
.

Definition build_entail_wit_13_1_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (STLevelPrefixBounds K_pre n_pre j (i + 1 ) )
.

Definition build_entail_wit_13_1_split_goal_4 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) 0))
.

Definition build_entail_wit_13_1_split_goal_5 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (a = (Znth (((i * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) 0))
.

Definition build_entail_wit_13_1_split_goal_6 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (STTableShape (replace_Znth (((i * K_pre ) + j )) (a) (st_l_2)) K_pre n_pre )
.

Definition build_entail_wit_13_2 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (IntArray.full st_pre (n_pre * K_pre ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) )
  **  (IntArray.full arr_pre n_pre l )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((i + len ) <= n_pre) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0)) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j (i + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  TT && emp 
|--
  “ (STLevelPrefix l (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre j (i + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevel l (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j (i + 1 ) ) ” 
  &&  “ (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) 0)) ” 
  &&  “ (a = (Znth (((i * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) 0)) ” 
  &&  “ (STTableShape (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre ) ”
  &&  emp
).

Definition build_entail_wit_13_2_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (STLevelPrefix l (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre j (i + 1 ) )
.

Definition build_entail_wit_13_2_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (STBuiltBeforeLevel l (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre j )
.

Definition build_entail_wit_13_2_split_goal_3 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (STLevelPrefixBounds K_pre n_pre j (i + 1 ) )
.

Definition build_entail_wit_13_2_split_goal_4 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) 0))
.

Definition build_entail_wit_13_2_split_goal_5 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (a = (Znth (((i * K_pre ) + j ) - 1 ) (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) 0))
.

Definition build_entail_wit_13_2_split_goal_6 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l_2 K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l_2 K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l_2 K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l_2 K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l_2 K_pre (i + half ) (j - 1 ) )) ,
  (STTableShape (replace_Znth (((i * K_pre ) + j )) (b) (st_l_2)) K_pre n_pre )
.

Definition build_entail_wit_14 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH11 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l_2 0))) (PreH12 : (STBuiltBeforeLevelBounds K_pre j )) (PreH13 : (STLevelPrefixBounds K_pre n_pre j (i + 1 ) )) (PreH14 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH15 : (STLevelPrefix l st_l_2 K_pre n_pre j (i + 1 ) )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j (i + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j (i + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition build_entail_wit_15 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) > n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (1 <= j) ” 
  &&  “ (j < K_pre) ” 
  &&  “ (half = (Power2 ((j - 1 )))) ” 
  &&  “ (len = (Power2 (j))) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre (j + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) > n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  TT && emp 
|--
  “ (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre (j + 1 ) ) ”
  &&  emp
).

Definition build_entail_wit_15_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) > n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )
.

Definition build_entail_wit_15_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : ((i + len ) > n_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH11 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) (PreH12 : (STLevelPrefix l st_l_2 K_pre n_pre j i )) ,
  (STBuiltBeforeLevelBounds K_pre (j + 1 ) )
.

Definition build_entail_wit_16 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (1 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= K_pre) ” 
  &&  “ (len = (Power2 (((j + 1 ) - 1 )))) ” 
  &&  “ ((len * 2 ) = (Power2 ((j + 1 )))) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre (j + 1 ) ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre (j + 1 ) ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )) ,
  TT && emp 
|--
  “ ((len * 2 ) = (Power2 ((j + 1 )))) ” 
  &&  “ (len = (Power2 (((j + 1 ) - 1 )))) ”
  &&  emp
).

Definition build_entail_wit_16_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )) ,
  ((len * 2 ) = (Power2 ((j + 1 ))))
.

Definition build_entail_wit_16_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (st_l_2: (@list Z)) (j: Z) (half: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l_2 K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (STBuiltBeforeLevelBounds K_pre (j + 1 ) )) (PreH9 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre (j + 1 ) )) ,
  (len = (Power2 (((j + 1 ) - 1 ))))
.

Definition build_return_wit_1 := 
(
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j >= K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l_2 )
|--
  EX (st_l: (@list Z)) ,
  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre K_pre ) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ”
  &&  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j >= K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) ,
  TT && emp 
|--
  “ (STBuilt l st_l_2 K_pre n_pre ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre K_pre ) ”
  &&  emp
).

Definition build_return_wit_1_split_goal_1 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j >= K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) ,
  (STBuilt l st_l_2 K_pre n_pre )
.

Definition build_return_wit_1_split_goal_2 := 
forall (K_pre: Z) (n_pre: Z) (l: (@list Z)) (len: Z) (half: Z) (j: Z) (st_l_2: (@list Z)) (PreH1 : (j >= K_pre)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l_2 K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j <= K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (STBuiltBeforeLevelBounds K_pre j )) (PreH10 : (STBuiltBeforeLevel l st_l_2 K_pre n_pre j )) ,
  (STBuiltBeforeLevelBounds K_pre K_pre )
.

Definition build_partial_solve_wit_1 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (idx: Z) (st_l: (@list Z)) (PreH1 : (idx < (n_pre * K_pre ))) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (0 <= idx)) (PreH6 : (idx <= (n_pre * K_pre ))) (PreH7 : (STZeroPrefixBounds st_l idx )) (PreH8 : (STZeroPrefix st_l idx )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (idx < (n_pre * K_pre )) ” 
  &&  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx <= (n_pre * K_pre )) ” 
  &&  “ (STZeroPrefixBounds st_l idx ) ” 
  &&  “ (STZeroPrefix st_l idx ) ”
  &&  (((st_pre + (idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre idx 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_2 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l K_pre i 0 )) (PreH10 : (STBasePrefix l st_l K_pre n_pre i )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (i * K_pre )) ” 
  &&  “ ((i * K_pre ) < (n_pre * K_pre )) ” 
  &&  “ (STBasePrefixBounds n_pre i ) ” 
  &&  “ (STCellBounds st_l K_pre i 0 ) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre i ) ”
  &&  (((arr_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i arr_pre i 0 n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition build_partial_solve_wit_3 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (0 <= i)) (PreH5 : (i < n_pre)) (PreH6 : (0 <= (i * K_pre ))) (PreH7 : ((i * K_pre ) < (n_pre * K_pre ))) (PreH8 : (STBasePrefixBounds n_pre i )) (PreH9 : (STCellBounds st_l K_pre i 0 )) (PreH10 : (STBasePrefix l st_l K_pre n_pre i )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (i * K_pre )) ” 
  &&  “ ((i * K_pre ) < (n_pre * K_pre )) ” 
  &&  “ (STBasePrefixBounds n_pre i ) ” 
  &&  “ (STCellBounds st_l K_pre i 0 ) ” 
  &&  “ (STBasePrefix l st_l K_pre n_pre i ) ”
  &&  (((st_pre + ((i * K_pre ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre (i * K_pre ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_4 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
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
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j i ) ” 
  &&  “ (STCellBounds st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre i j ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ”
  &&  (((st_pre + ((((i * K_pre ) + j ) - 1 ) * sizeof(INT)))) # Int  |-> (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))
  **  (IntArray.missing_i st_pre (((i * K_pre ) + j ) - 1 ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_5 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (RMQInputValues l n_pre )) (PreH3 : (STTableShape st_l K_pre n_pre )) (PreH4 : (1 <= j)) (PreH5 : (j < K_pre)) (PreH6 : (half = (Power2 ((j - 1 ))))) (PreH7 : (len = (Power2 (j)))) (PreH8 : (0 <= i)) (PreH9 : ((i + len ) <= n_pre)) (PreH10 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH11 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH13 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH14 : (0 <= ((i * K_pre ) + j ))) (PreH15 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH16 : (STBuiltBeforeLevelBounds K_pre j )) (PreH17 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH18 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH19 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH20 : (STCellBounds st_l K_pre i j )) (PreH21 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH22 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH23 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH24 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
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
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j i ) ” 
  &&  “ (STCellBounds st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre i j ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ”
  &&  (((st_pre + (((((i + half ) * K_pre ) + j ) - 1 ) * sizeof(INT)))) # Int  |-> (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))
  **  (IntArray.missing_i st_pre ((((i + half ) * K_pre ) + j ) - 1 ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_6 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (a >= b) ” 
  &&  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
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
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j i ) ” 
  &&  “ (STCellBounds st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre i j ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ”
  &&  (((st_pre + (((i * K_pre ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre ((i * K_pre ) + j ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

Definition build_partial_solve_wit_7 := 
forall (st_pre: Z) (K_pre: Z) (n_pre: Z) (arr_pre: Z) (l: (@list Z)) (st_l: (@list Z)) (j: Z) (half: Z) (len: Z) (i: Z) (a: Z) (b: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (RMQInputValues l n_pre )) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (1 <= j)) (PreH6 : (j < K_pre)) (PreH7 : (half = (Power2 ((j - 1 ))))) (PreH8 : (len = (Power2 (j)))) (PreH9 : (0 <= i)) (PreH10 : ((i + len ) <= n_pre)) (PreH11 : (0 <= (((i * K_pre ) + j ) - 1 ))) (PreH12 : ((((i * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH13 : (0 <= ((((i + half ) * K_pre ) + j ) - 1 ))) (PreH14 : (((((i + half ) * K_pre ) + j ) - 1 ) < (n_pre * K_pre ))) (PreH15 : (0 <= ((i * K_pre ) + j ))) (PreH16 : (((i * K_pre ) + j ) < (n_pre * K_pre ))) (PreH17 : (a = (Znth (((i * K_pre ) + j ) - 1 ) st_l 0))) (PreH18 : (b = (Znth ((((i + half ) * K_pre ) + j ) - 1 ) st_l 0))) (PreH19 : (STBuiltBeforeLevelBounds K_pre j )) (PreH20 : (STLevelPrefixBounds K_pre n_pre j i )) (PreH21 : (STCellBounds st_l K_pre i (j - 1 ) )) (PreH22 : (STCellBounds st_l K_pre (i + half ) (j - 1 ) )) (PreH23 : (STCellBounds st_l K_pre i j )) (PreH24 : (STBuiltBeforeLevel l st_l K_pre n_pre j )) (PreH25 : (STLevelPrefix l st_l K_pre n_pre j i )) (PreH26 : (STCellRangeMax l st_l K_pre i (j - 1 ) )) (PreH27 : (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) )) ,
  (IntArray.full arr_pre n_pre l )
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (a < b) ” 
  &&  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (RMQInputValues l n_pre ) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
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
  &&  “ (STBuiltBeforeLevelBounds K_pre j ) ” 
  &&  “ (STLevelPrefixBounds K_pre n_pre j i ) ” 
  &&  “ (STCellBounds st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre (i + half ) (j - 1 ) ) ” 
  &&  “ (STCellBounds st_l K_pre i j ) ” 
  &&  “ (STBuiltBeforeLevel l st_l K_pre n_pre j ) ” 
  &&  “ (STLevelPrefix l st_l K_pre n_pre j i ) ” 
  &&  “ (STCellRangeMax l st_l K_pre i (j - 1 ) ) ” 
  &&  “ (STCellRangeMax l st_l K_pre (i + half ) (j - 1 ) ) ”
  &&  (((st_pre + (((i * K_pre ) + j ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i st_pre ((i * K_pre ) + j ) 0 (n_pre * K_pre ) st_l )
  **  (IntArray.full arr_pre n_pre l )
.

(*----- Function query -----*)

Definition query_safety_wit_1 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (((right_pre - left_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right_pre - left_pre ) + 1 )) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (((right_pre - left_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((right_pre - left_pre ) + 1 )) ”
).

Definition query_safety_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (((right_pre - left_pre ) + 1 ) <= INT_MAX) ”
.

Definition query_safety_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= ((right_pre - left_pre ) + 1 )) ”
.

Definition query_safety_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((right_pre - left_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right_pre - left_pre )) ”
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((right_pre - left_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (right_pre - left_pre )) ”
).

Definition query_safety_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((right_pre - left_pre ) <= INT_MAX) ”
.

Definition query_safety_wit_2_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ ((INT_MIN) <= (right_pre - left_pre )) ”
.

Definition query_safety_wit_3 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> ((right_pre - left_pre ) + 1 ))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition query_safety_wit_5 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  ((( &( "pow" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> ((right_pre - left_pre ) + 1 ))
  **  ((( &( "st" ) )) # Ptr  |-> st_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "K" ) )) # Int  |-> K_pre)
  **  ((( &( "left" ) )) # Int  |-> left_pre)
  **  ((( &( "right" ) )) # Int  |-> right_pre)
  **  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition query_safety_wit_6 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
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
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
).

Definition query_safety_wit_11_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
.

Definition query_safety_wit_11_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
  “ ((INT_MIN) <= ((left_pre * K_pre ) + k )) ”
.

Definition query_safety_wit_12 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
).

Definition query_safety_wit_12_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
.

Definition query_safety_wit_12_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
  “ ((INT_MIN) <= (left_pre * K_pre )) ”
.

Definition query_safety_wit_13 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
).

Definition query_safety_wit_13_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
.

Definition query_safety_wit_13_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
  “ ((INT_MIN) <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ”
.

Definition query_safety_wit_14 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
).

Definition query_safety_wit_14_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
.

Definition query_safety_wit_14_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
  “ ((INT_MIN) <= (((right_pre - pow ) + 1 ) * K_pre )) ”
.

Definition query_safety_wit_15 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
).

Definition query_safety_wit_15_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
.

Definition query_safety_wit_15_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
  “ ((INT_MIN) <= ((right_pre - pow ) + 1 )) ”
.

Definition query_safety_wit_16 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
).

Definition query_safety_wit_16_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
.

Definition query_safety_wit_16_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
  “ ((INT_MIN) <= (right_pre - pow )) ”
.

Definition query_safety_wit_17 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
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
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (QueryIntervalBounds n_pre left_pre right_pre ) ” 
  &&  “ (((right_pre - left_pre ) + 1 ) = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre K_pre ) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogBounds K_pre n_pre ((right_pre - left_pre ) + 1 ) 0 1 ) ” 
  &&  “ (QueryLogLoopState ((right_pre - left_pre ) + 1 ) 0 1 ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  TT && emp 
|--
  “ (QueryLogLoopState ((right_pre - left_pre ) + 1 ) 0 1 ) ” 
  &&  “ (QueryLogBounds K_pre n_pre ((right_pre - left_pre ) + 1 ) 0 1 ) ”
  &&  emp
).

Definition query_entail_wit_1_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  (QueryLogLoopState ((right_pre - left_pre ) + 1 ) 0 1 )
.

Definition query_entail_wit_1_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (STTableShape st_l K_pre n_pre )) (PreH5 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH6 : (STBuilt l st_l K_pre n_pre )) ,
  (QueryLogBounds K_pre n_pre ((right_pre - left_pre ) + 1 ) 0 1 )
.

Definition query_entail_wit_2 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (QueryIntervalBounds n_pre left_pre right_pre ) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre K_pre ) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogBounds K_pre n_pre len (k + 1 ) (pow * 2 ) ) ” 
  &&  “ (QueryLogLoopState len (k + 1 ) (pow * 2 ) ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  TT && emp 
|--
  “ (QueryLogLoopState ((right_pre - left_pre ) + 1 ) (k + 1 ) (pow * 2 ) ) ” 
  &&  “ (QueryLogBounds K_pre n_pre ((right_pre - left_pre ) + 1 ) (k + 1 ) (pow * 2 ) ) ”
  &&  emp
).

Definition query_entail_wit_2_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (QueryLogLoopState ((right_pre - left_pre ) + 1 ) (k + 1 ) (pow * 2 ) )
.

Definition query_entail_wit_2_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) <= len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (QueryLogBounds K_pre n_pre ((right_pre - left_pre ) + 1 ) (k + 1 ) (pow * 2 ) )
.

Definition query_entail_wit_3 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (QueryIntervalBounds n_pre left_pre right_pre ) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre K_pre ) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogBounds K_pre n_pre len k pow ) ” 
  &&  “ (QueryLogFinalState len k pow ) ” 
  &&  “ (0 <= ((left_pre * K_pre ) + k )) ” 
  &&  “ (((left_pre * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ” 
  &&  “ (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (STCellBounds st_l K_pre left_pre k ) ” 
  &&  “ (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre left_pre k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  TT && emp 
|--
  “ (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre left_pre k ) ” 
  &&  “ (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k ) ” 
  &&  “ (STCellBounds st_l K_pre left_pre k ) ” 
  &&  “ (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ” 
  &&  “ (((left_pre * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((left_pre * K_pre ) + k )) ” 
  &&  “ (QueryLogFinalState ((right_pre - left_pre ) + 1 ) k pow ) ”
  &&  emp
).

Definition query_entail_wit_3_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )
.

Definition query_entail_wit_3_split_goal_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (STCellRangeMax l st_l K_pre left_pre k )
.

Definition query_entail_wit_3_split_goal_3 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )
.

Definition query_entail_wit_3_split_goal_4 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (STCellBounds st_l K_pre left_pre k )
.

Definition query_entail_wit_3_split_goal_5 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))
.

Definition query_entail_wit_3_split_goal_6 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))
.

Definition query_entail_wit_3_split_goal_7 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))
.

Definition query_entail_wit_3_split_goal_8 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (0 <= ((left_pre * K_pre ) + k ))
.

Definition query_entail_wit_3_split_goal_9 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (k: Z) (pow: Z) (len: Z) (PreH1 : ((pow * 2 ) > len)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH8 : (STBuilt l st_l K_pre n_pre )) (PreH9 : (QueryLogBounds K_pre n_pre len k pow )) (PreH10 : (QueryLogLoopState len k pow )) ,
  (QueryLogFinalState ((right_pre - left_pre ) + 1 ) k pow )
.

Definition query_entail_wit_4 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (QueryIntervalBounds n_pre left_pre right_pre ) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ ((Znth ((left_pre * K_pre ) + k ) st_l 0) = (Znth ((left_pre * K_pre ) + k ) st_l 0)) ” 
  &&  “ ((Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0) = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0)) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre K_pre ) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogBounds K_pre n_pre len k pow ) ” 
  &&  “ (QueryLogFinalState len k pow ) ” 
  &&  “ (STCellBounds st_l K_pre left_pre k ) ” 
  &&  “ (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre left_pre k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition query_entail_wit_5 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH8 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH10 : (STBuilt l st_l K_pre n_pre )) (PreH11 : (QueryLogBounds K_pre n_pre len k pow )) (PreH12 : (QueryLogFinalState len k pow )) (PreH13 : (STCellBounds st_l K_pre left_pre k )) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (QueryIntervalBounds n_pre left_pre right_pre ) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (a = (Znth ((left_pre * K_pre ) + k ) st_l 0)) ” 
  &&  “ (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0)) ” 
  &&  “ (QueryLogBounds K_pre n_pre len k pow ) ” 
  &&  “ (QueryLogFinalState len k pow ) ” 
  &&  “ (RangeMaxValue l left_pre (right_pre + 1 ) a ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH8 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH10 : (STBuilt l st_l K_pre n_pre )) (PreH11 : (QueryLogBounds K_pre n_pre len k pow )) (PreH12 : (QueryLogFinalState len k pow )) (PreH13 : (STCellBounds st_l K_pre left_pre k )) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  TT && emp 
|--
  “ (RangeMaxValue l left_pre (right_pre + 1 ) a ) ”
  &&  emp
).

Definition query_entail_wit_5_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a >= b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH8 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH10 : (STBuilt l st_l K_pre n_pre )) (PreH11 : (QueryLogBounds K_pre n_pre len k pow )) (PreH12 : (QueryLogFinalState len k pow )) (PreH13 : (STCellBounds st_l K_pre left_pre k )) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (RangeMaxValue l left_pre (right_pre + 1 ) a )
.

Definition query_entail_wit_6 := 
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH8 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH10 : (STBuilt l st_l K_pre n_pre )) (PreH11 : (QueryLogBounds K_pre n_pre len k pow )) (PreH12 : (QueryLogFinalState len k pow )) (PreH13 : (STCellBounds st_l K_pre left_pre k )) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (QueryIntervalBounds n_pre left_pre right_pre ) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (a = (Znth ((left_pre * K_pre ) + k ) st_l 0)) ” 
  &&  “ (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0)) ” 
  &&  “ (QueryLogBounds K_pre n_pre len k pow ) ” 
  &&  “ (QueryLogFinalState len k pow ) ” 
  &&  “ (RangeMaxValue l left_pre (right_pre + 1 ) b ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
) \/
(
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH8 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH10 : (STBuilt l st_l K_pre n_pre )) (PreH11 : (QueryLogBounds K_pre n_pre len k pow )) (PreH12 : (QueryLogFinalState len k pow )) (PreH13 : (STCellBounds st_l K_pre left_pre k )) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  TT && emp 
|--
  “ (RangeMaxValue l left_pre (right_pre + 1 ) b ) ”
  &&  emp
).

Definition query_entail_wit_6_split_goal_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (a < b)) (PreH2 : (RMQSizeSafe n_pre K_pre )) (PreH3 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH4 : (len = ((right_pre - left_pre ) + 1 ))) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (STTableShape st_l K_pre n_pre )) (PreH7 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH8 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH9 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH10 : (STBuilt l st_l K_pre n_pre )) (PreH11 : (QueryLogBounds K_pre n_pre len k pow )) (PreH12 : (QueryLogFinalState len k pow )) (PreH13 : (STCellBounds st_l K_pre left_pre k )) (PreH14 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH15 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH16 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (RangeMaxValue l left_pre (right_pre + 1 ) b )
.

Definition query_return_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH7 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (RangeMaxValue l left_pre (right_pre + 1 ) b )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RangeMaxValue l left_pre (right_pre + 1 ) b ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition query_return_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (a: Z) (k: Z) (b: Z) (pow: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (a = (Znth ((left_pre * K_pre ) + k ) st_l 0))) (PreH7 : (b = (Znth ((((right_pre - pow ) + 1 ) * K_pre ) + k ) st_l 0))) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (RangeMaxValue l left_pre (right_pre + 1 ) a )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RangeMaxValue l left_pre (right_pre + 1 ) a ) ”
  &&  (IntArray.full st_pre (n_pre * K_pre ) st_l )
.

Definition query_partial_solve_wit_1 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (QueryIntervalBounds n_pre left_pre right_pre ) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre K_pre ) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogBounds K_pre n_pre len k pow ) ” 
  &&  “ (QueryLogFinalState len k pow ) ” 
  &&  “ (0 <= ((left_pre * K_pre ) + k )) ” 
  &&  “ (((left_pre * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ” 
  &&  “ (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (STCellBounds st_l K_pre left_pre k ) ” 
  &&  “ (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre left_pre k ) ” 
  &&  “ (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k ) ”
  &&  (((st_pre + (((left_pre * K_pre ) + k ) * sizeof(INT)))) # Int  |-> (Znth ((left_pre * K_pre ) + k ) st_l 0))
  **  (IntArray.missing_i st_pre ((left_pre * K_pre ) + k ) 0 (n_pre * K_pre ) st_l )
.

Definition query_partial_solve_wit_2 := 
forall (right_pre: Z) (left_pre: Z) (K_pre: Z) (n_pre: Z) (st_pre: Z) (st_l: (@list Z)) (l: (@list Z)) (len: Z) (pow: Z) (k: Z) (PreH1 : (RMQSizeSafe n_pre K_pre )) (PreH2 : (QueryIntervalBounds n_pre left_pre right_pre )) (PreH3 : (len = ((right_pre - left_pre ) + 1 ))) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (STTableShape st_l K_pre n_pre )) (PreH6 : (STBuiltBeforeLevelBounds K_pre K_pre )) (PreH7 : (STBuilt l st_l K_pre n_pre )) (PreH8 : (QueryLogBounds K_pre n_pre len k pow )) (PreH9 : (QueryLogFinalState len k pow )) (PreH10 : (0 <= ((left_pre * K_pre ) + k ))) (PreH11 : (((left_pre * K_pre ) + k ) < (n_pre * K_pre ))) (PreH12 : (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k ))) (PreH13 : (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre ))) (PreH14 : (STCellBounds st_l K_pre left_pre k )) (PreH15 : (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k )) (PreH16 : (STCellRangeMax l st_l K_pre left_pre k )) (PreH17 : (STCellRangeMax l st_l K_pre ((right_pre - pow ) + 1 ) k )) ,
  (IntArray.full st_pre (n_pre * K_pre ) st_l )
|--
  “ (RMQSizeSafe n_pre K_pre ) ” 
  &&  “ (QueryIntervalBounds n_pre left_pre right_pre ) ” 
  &&  “ (len = ((right_pre - left_pre ) + 1 )) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (STTableShape st_l K_pre n_pre ) ” 
  &&  “ (STBuiltBeforeLevelBounds K_pre K_pre ) ” 
  &&  “ (STBuilt l st_l K_pre n_pre ) ” 
  &&  “ (QueryLogBounds K_pre n_pre len k pow ) ” 
  &&  “ (QueryLogFinalState len k pow ) ” 
  &&  “ (0 <= ((left_pre * K_pre ) + k )) ” 
  &&  “ (((left_pre * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (0 <= ((((right_pre - pow ) + 1 ) * K_pre ) + k )) ” 
  &&  “ (((((right_pre - pow ) + 1 ) * K_pre ) + k ) < (n_pre * K_pre )) ” 
  &&  “ (STCellBounds st_l K_pre left_pre k ) ” 
  &&  “ (STCellBounds st_l K_pre ((right_pre - pow ) + 1 ) k ) ” 
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
