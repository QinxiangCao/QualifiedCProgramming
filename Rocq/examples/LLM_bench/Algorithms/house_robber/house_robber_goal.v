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
Require Import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function rob -----*)

Definition rob_safety_wit_1 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((( &( "prev2" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rob_safety_wit_2 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((( &( "prev1" ) )) # Int  |->_)
  **  ((( &( "prev2" ) )) # Int  |-> 0)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rob_safety_wit_3 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "prev1" ) )) # Int  |-> 0)
  **  ((( &( "prev2" ) )) # Int  |-> 0)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rob_safety_wit_4 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : (0 <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
  **  ((( &( "take" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev2" ) )) # Int  |-> prev2)
  **  ((( &( "prev1" ) )) # Int  |-> prev1)
|--
  “ ((prev2 + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prev2 + (Znth i l 0) )) ”
.

Definition rob_safety_wit_5 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (take: Z) (prev2: Z) (skip: Z) (prev1: Z) (cur: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (take = (prev2 + (Znth i l 0) ))) (PreH8 : (skip = prev1)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (0 <= cur)) (PreH14 : (cur <= 1000000000)) (PreH15 : (HouseRobberDPState l (i + 1 ) prev1 cur )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "prev2" ) )) # Int  |-> prev1)
  **  ((( &( "prev1" ) )) # Int  |-> cur)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition rob_entail_wit_1 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1000000000) ” 
  &&  “ (HouseRobberDPState l 0 0 0 ) ”
  &&  (IntArray.full nums_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (HouseRobberDPState l 0 0 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  emp
).

Definition rob_entail_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  (HouseRobberDPState l 0 0 0 )
.

Definition rob_entail_wit_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))
.

Definition rob_entail_wit_2_1 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((prev2 + (Znth i l 0) ) = (prev2 + (Znth i l 0) )) ” 
  &&  “ (prev1 = prev1) ” 
  &&  “ (0 <= prev2) ” 
  &&  “ (prev2 <= 1000000000) ” 
  &&  “ (0 <= prev1) ” 
  &&  “ (prev1 <= 1000000000) ” 
  &&  “ (0 <= (prev2 + (Znth i l 0) )) ” 
  &&  “ ((prev2 + (Znth i l 0) ) <= 1000000000) ” 
  &&  “ (HouseRobberDPState l (i + 1 ) prev1 (prev2 + (Znth i l 0) ) ) ”
  &&  (IntArray.full nums_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1 )) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (i + 1 ) prev1 (prev2 + (Znth i l 0) ) ) ” 
  &&  “ ((prev2 + (Znth i l 0) ) <= 1000000000) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  emp
).

Definition rob_entail_wit_2_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1 )) ,
  (HouseRobberDPState l (i + 1 ) prev1 (prev2 + (Znth i l 0) ) )
.

Definition rob_entail_wit_2_1_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1 )) ,
  ((prev2 + (Znth i l 0) ) <= 1000000000)
.

Definition rob_entail_wit_2_1_split_goal_3 := 
forall (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))
.

Definition rob_entail_wit_2_2 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ ((prev2 + (Znth i l 0) ) = (prev2 + (Znth i l 0) )) ” 
  &&  “ (prev1 = prev1) ” 
  &&  “ (0 <= prev2) ” 
  &&  “ (prev2 <= 1000000000) ” 
  &&  “ (0 <= prev1) ” 
  &&  “ (prev1 <= 1000000000) ” 
  &&  “ (0 <= prev1) ” 
  &&  “ (prev1 <= 1000000000) ” 
  &&  “ (HouseRobberDPState l (i + 1 ) prev1 prev1 ) ”
  &&  (IntArray.full nums_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1 )) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (i + 1 ) prev1 prev1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  emp
).

Definition rob_entail_wit_2_2_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1 )) ,
  (HouseRobberDPState l (i + 1 ) prev1 prev1 )
.

Definition rob_entail_wit_2_2_split_goal_2 := 
forall (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : ((prev2 + (Znth i l 0) ) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (0 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (HouseRobberDPState l i prev2 prev1 )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))
.

Definition rob_entail_wit_3 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (i: Z) (take: Z) (prev2: Z) (skip: Z) (prev1: Z) (cur: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (take = (prev2 + (Znth i l 0) ))) (PreH8 : (skip = prev1)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (0 <= cur)) (PreH14 : (cur <= 1000000000)) (PreH15 : (HouseRobberDPState l (i + 1 ) prev1 cur )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= prev1) ” 
  &&  “ (prev1 <= 1000000000) ” 
  &&  “ (0 <= cur) ” 
  &&  “ (cur <= 1000000000) ” 
  &&  “ (HouseRobberDPState l (i + 1 ) prev1 cur ) ”
  &&  (IntArray.full nums_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (i: Z) (take: Z) (prev2: Z) (skip: Z) (prev1: Z) (cur: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (take = (prev2 + (Znth i l 0) ))) (PreH8 : (skip = prev1)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (0 <= cur)) (PreH14 : (cur <= 1000000000)) (PreH15 : (HouseRobberDPState l (i + 1 ) prev1 cur )) ,
  TT && emp 
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ”
  &&  emp
).

Definition rob_entail_wit_3_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (i: Z) (take: Z) (prev2: Z) (skip: Z) (prev1: Z) (cur: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((0 <= (Znth k_2 l 0)) /\ ((Znth k_2 l 0) <= 10000)))) (PreH5 : (0 <= i)) (PreH6 : (i < n_pre)) (PreH7 : (take = (prev2 + (Znth i l 0) ))) (PreH8 : (skip = prev1)) (PreH9 : (0 <= prev2)) (PreH10 : (prev2 <= 1000000000)) (PreH11 : (0 <= prev1)) (PreH12 : (prev1 <= 1000000000)) (PreH13 : (0 <= cur)) (PreH14 : (cur <= 1000000000)) (PreH15 : (HouseRobberDPState l (i + 1 ) prev1 cur )) ,
  forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))
.

Definition rob_return_wit_1 := 
(
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : (0 <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (HouseRobberAnswer l prev1 ) ” 
  &&  “ (0 <= prev1) ” 
  &&  “ (prev1 <= 1000000000) ”
  &&  (IntArray.full nums_pre n_pre l )
) \/
(
forall (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : (0 <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1 )) ,
  TT && emp 
|--
  “ (HouseRobberAnswer l prev1 ) ”
  &&  emp
).

Definition rob_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : (i >= n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : (0 <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1 )) ,
  (HouseRobberAnswer l prev1 )
.

Definition rob_partial_solve_wit_1 := 
forall (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (prev1: Z) (prev2: Z) (i: Z) (PreH1 : (i < n_pre)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000)))) (PreH6 : (0 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (0 <= prev2)) (PreH9 : (prev2 <= 1000000000)) (PreH10 : (0 <= prev1)) (PreH11 : (prev1 <= 1000000000)) (PreH12 : (HouseRobberDPState l i prev2 prev1 )) ,
  (IntArray.full nums_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((0 <= (Znth k l 0)) /\ ((Znth k l 0) <= 10000))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= prev2) ” 
  &&  “ (prev2 <= 1000000000) ” 
  &&  “ (0 <= prev1) ” 
  &&  “ (prev1 <= 1000000000) ” 
  &&  “ (HouseRobberDPState l i prev2 prev1 ) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_rob_safety_wit_1 : rob_safety_wit_1.
Axiom proof_of_rob_safety_wit_2 : rob_safety_wit_2.
Axiom proof_of_rob_safety_wit_3 : rob_safety_wit_3.
Axiom proof_of_rob_safety_wit_4 : rob_safety_wit_4.
Axiom proof_of_rob_safety_wit_5 : rob_safety_wit_5.
Axiom proof_of_rob_entail_wit_1 : rob_entail_wit_1.
Axiom proof_of_rob_entail_wit_2_1 : rob_entail_wit_2_1.
Axiom proof_of_rob_entail_wit_2_2 : rob_entail_wit_2_2.
Axiom proof_of_rob_entail_wit_3 : rob_entail_wit_3.
Axiom proof_of_rob_return_wit_1 : rob_return_wit_1.
Axiom proof_of_rob_partial_solve_wit_1 : rob_partial_solve_wit_1.

End VC_Correct.
