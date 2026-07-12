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
Require Import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function maxSlidingWindow -----*)

Definition maxSlidingWindow_safety_wit_1 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (q0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "head" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_2 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (q0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "tail" ) )) # Int  |->_)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_3 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (q0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "out_idx" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Int  |-> 0)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_4 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (q0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out_idx" ) )) # Int  |-> 0)
  **  ((( &( "tail" ) )) # Int  |-> 0)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q0 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_5 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH17 : (SWMQueueDropLoopState l q_l head tail i k_pre )) (PreH18 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH19 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH20 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH21 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH22 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full q_pre n_pre q_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  “ ((i - k_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - k_pre )) ”
.

Definition maxSlidingWindow_safety_wit_6 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : ((Znth head q_l 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH18 : (SWMQueueDropLoopState l q_l head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full q_pre n_pre q_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  “ ((head + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (head + 1 )) ”
.

Definition maxSlidingWindow_safety_wit_7 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH17 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH18 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH19 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ ((tail - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail - 1 )) ”
.

Definition maxSlidingWindow_safety_wit_8 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH17 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH18 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH19 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition maxSlidingWindow_safety_wit_9 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH18 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) (PreH21 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH22 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH23 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full q_pre n_pre q_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  “ ((tail - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail - 1 )) ”
.

Definition maxSlidingWindow_safety_wit_10 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH16 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH17 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) (PreH19 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH20 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH21 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l 0) l 0) > (Znth i l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full q_pre n_pre (replace_Znth (tail) (i) (q_l)) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  “ ((tail + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail + 1 )) ”
.

Definition maxSlidingWindow_safety_wit_11 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH16 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH17 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH18 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ ((k_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k_pre - 1 )) ”
.

Definition maxSlidingWindow_safety_wit_12 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH16 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH17 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH18 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition maxSlidingWindow_safety_wit_13 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (out_idx = ((i - k_pre ) + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH14 : (SWMOutputPrefix l k_pre (out_idx + 1 ) out_l )) (PreH15 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH16 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH17 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 (out_idx + 1 ) out_l )
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ ((out_idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_idx + 1 )) ”
.

Definition maxSlidingWindow_safety_wit_14 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : (((i + 1 ) < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= (i + 1 )) -> (out_idx = (((i + 1 ) - k_pre ) + 1 )))) (PreH15 : ((k_pre <= (i + 1 )) -> (head < tail))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH17 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH18 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH19 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "q" ) )) # Ptr  |-> q_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition maxSlidingWindow_entail_wit_1 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (q0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q0 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((0 < k_pre) -> (0 = 0)) ” 
  &&  “ ((k_pre <= 0) -> (0 = ((0 - k_pre ) + 1 ))) ” 
  &&  “ ((k_pre <= 0) -> (0 < 0)) ” 
  &&  “ (SWMOutputPrefix l k_pre 0 out_l ) ” 
  &&  “ (SWMQueueState l q_l 0 0 0 k_pre ) ” 
  &&  “ forall (pos: Z) , (((0 <= pos) /\ (pos < 0)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 0 out_l )
  **  (IntArray.undef_seg out_pre 0 ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (q0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (SWMQueueState l q0 0 0 0 k_pre ) ” 
  &&  “ (SWMOutputPrefix l k_pre 0 (@nil Z) ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (q0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (SWMQueueState l q0 0 0 0 k_pre )
.

Definition maxSlidingWindow_entail_wit_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (q0: (@list Z)) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q0)) = n_pre)) (PreH6 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (SWMOutputPrefix l k_pre 0 (@nil Z) )
.

Definition maxSlidingWindow_entail_wit_2 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueDropLoopState l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0))) ” 
  &&  “ ((((i - k_pre ) <= (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < i)) /\ (((i - k_pre ) <= (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < i))) ” 
  &&  “ (SWMQueueDropLoopState l q_l_2 head tail i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))
.

Definition maxSlidingWindow_entail_wit_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))
.

Definition maxSlidingWindow_entail_wit_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  ((((i - k_pre ) <= (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < i)) /\ (((i - k_pre ) <= (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < i)))
.

Definition maxSlidingWindow_entail_wit_2_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (SWMQueueDropLoopState l q_l_2 head tail i k_pre )
.

Definition maxSlidingWindow_entail_wit_3 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full q_pre n_pre q_l_2 )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= (head + 1 )) ” 
  &&  “ ((head + 1 ) <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueDropLoopState l q_l (head + 1 ) tail i k_pre ) ” 
  &&  “ forall (pos: Z) , ((((head + 1 ) <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , ((((head + 1 ) <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , (((((head + 1 ) <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , (((((head + 1 ) <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  TT && emp 
|--
  “ ((((i - k_pre ) <= (Znth (head + 1 ) q_l_2 0)) /\ ((Znth (head + 1 ) q_l_2 0) < i)) /\ (((i - k_pre ) <= (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < i))) ” 
  &&  “ (((0 <= (Znth (head + 1 ) q_l_2 0)) /\ ((Znth (head + 1 ) q_l_2 0) < n_pre)) /\ ((0 <= (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre))) ” 
  &&  “ (SWMQueueDropLoopState l q_l_2 (head + 1 ) tail i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_3_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((((i - k_pre ) <= (Znth (head + 1 ) q_l_2 0)) /\ ((Znth (head + 1 ) q_l_2 0) < i)) /\ (((i - k_pre ) <= (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < i)))
.

Definition maxSlidingWindow_entail_wit_3_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (((0 <= (Znth (head + 1 ) q_l_2 0)) /\ ((Znth (head + 1 ) q_l_2 0) < n_pre)) /\ ((0 <= (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))
.

Definition maxSlidingWindow_entail_wit_3_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (SWMQueueDropLoopState l q_l_2 (head + 1 ) tail i k_pre )
.

Definition maxSlidingWindow_entail_wit_4_1 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full q_pre n_pre q_l_2 )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueAfterDrop l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0))) ” 
  &&  “ ((((i - k_pre ) < (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < i)) /\ (((i - k_pre ) < (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < i))) ” 
  &&  “ (SWMQueueAfterDrop l q_l_2 head tail i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_4_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))
.

Definition maxSlidingWindow_entail_wit_4_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))
.

Definition maxSlidingWindow_entail_wit_4_1_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  ((((i - k_pre ) < (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < i)) /\ (((i - k_pre ) < (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < i)))
.

Definition maxSlidingWindow_entail_wit_4_1_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (SWMQueueAfterDrop l q_l_2 head tail i k_pre )
.

Definition maxSlidingWindow_entail_wit_4_2 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueAfterDrop l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0))) ” 
  &&  “ ((((i - k_pre ) < (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < i)) /\ (((i - k_pre ) < (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < i))) ” 
  &&  “ (SWMQueueAfterDrop l q_l_2 head tail i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_4_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))
.

Definition maxSlidingWindow_entail_wit_4_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))
.

Definition maxSlidingWindow_entail_wit_4_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  ((((i - k_pre ) < (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < i)) /\ (((i - k_pre ) < (Znth (tail - 1 ) q_l_2 0)) /\ ((Znth (tail - 1 ) q_l_2 0) < i)))
.

Definition maxSlidingWindow_entail_wit_4_2_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) <= (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (SWMQueueAfterDrop l q_l_2 head tail i k_pre )
.

Definition maxSlidingWindow_entail_wit_5 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueueAfterDrop l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueueAfterDrop l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0))) ” 
  &&  “ (SWMQueuePendingState l q_l_2 head tail i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_5_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueueAfterDrop l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))
.

Definition maxSlidingWindow_entail_wit_5_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueueAfterDrop l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))
.

Definition maxSlidingWindow_entail_wit_5_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueueAfterDrop l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH20 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH21 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH22 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (SWMQueuePendingState l q_l_2 head tail i k_pre )
.

Definition maxSlidingWindow_entail_wit_6 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH22 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH23 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full q_pre n_pre q_l_2 )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= (tail - 1 )) ” 
  &&  “ ((tail - 1 ) <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head (tail - 1 ) i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < (tail - 1 ))) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < (tail - 1 )) -> ((((0 <= ((tail - 1 ) - 1 )) /\ (((tail - 1 ) - 1 ) < n_pre)) /\ (0 <= (Znth ((tail - 1 ) - 1 ) q_l 0))) /\ ((Znth ((tail - 1 ) - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < (tail - 1 ))) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < (tail - 1 ))) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < (tail - 1 ))) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH22 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH23 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  TT && emp 
|--
  “ ((((i - k_pre ) < (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < i)) /\ (((i - k_pre ) < (Znth ((tail - 1 ) - 1 ) q_l_2 0)) /\ ((Znth ((tail - 1 ) - 1 ) q_l_2 0) < i))) ” 
  &&  “ ((head < (tail - 1 )) -> ((((0 <= ((tail - 1 ) - 1 )) /\ (((tail - 1 ) - 1 ) < n_pre)) /\ (0 <= (Znth ((tail - 1 ) - 1 ) q_l_2 0))) /\ ((Znth ((tail - 1 ) - 1 ) q_l_2 0) < n_pre))) ” 
  &&  “ (((0 <= (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < n_pre)) /\ ((0 <= (Znth ((tail - 1 ) - 1 ) q_l_2 0)) /\ ((Znth ((tail - 1 ) - 1 ) q_l_2 0) < n_pre))) ” 
  &&  “ (SWMQueuePendingState l q_l_2 head (tail - 1 ) i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_6_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH22 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH23 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((((i - k_pre ) < (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < i)) /\ (((i - k_pre ) < (Znth ((tail - 1 ) - 1 ) q_l_2 0)) /\ ((Znth ((tail - 1 ) - 1 ) q_l_2 0) < i)))
.

Definition maxSlidingWindow_entail_wit_6_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH22 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH23 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  ((head < (tail - 1 )) -> ((((0 <= ((tail - 1 ) - 1 )) /\ (((tail - 1 ) - 1 ) < n_pre)) /\ (0 <= (Znth ((tail - 1 ) - 1 ) q_l_2 0))) /\ ((Znth ((tail - 1 ) - 1 ) q_l_2 0) < n_pre)))
.

Definition maxSlidingWindow_entail_wit_6_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH22 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH23 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (((0 <= (Znth head q_l_2 0)) /\ ((Znth head q_l_2 0) < n_pre)) /\ ((0 <= (Znth ((tail - 1 ) - 1 ) q_l_2 0)) /\ ((Znth ((tail - 1 ) - 1 ) q_l_2 0) < n_pre)))
.

Definition maxSlidingWindow_entail_wit_6_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < i)))) (PreH22 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH23 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH24 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (SWMQueuePendingState l q_l_2 head (tail - 1 ) i k_pre )
.

Definition maxSlidingWindow_entail_wit_7_1 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH22 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH23 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH24 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full q_pre n_pre q_l_2 )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l 0) l 0) > (Znth i l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH22 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH23 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH24 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0))) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_7_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH22 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH23 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH24 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))
.

Definition maxSlidingWindow_entail_wit_7_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH20 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH21 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH22 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH23 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH24 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))
.

Definition maxSlidingWindow_entail_wit_7_2 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l 0) l 0) > (Znth i l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0))) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_7_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))
.

Definition maxSlidingWindow_entail_wit_7_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH18 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> ((0 <= (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < n_pre)))) (PreH19 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH20 : forall (pos_4: Z) , (((head <= pos_4) /\ (pos_4 < tail)) -> (((i - k_pre ) < (Znth pos_4 q_l_2 0)) /\ ((Znth pos_4 q_l_2 0) < i)))) (PreH21 : forall (p_3: Z) , forall (r_3: Z) , ((((head <= p_3) /\ (p_3 < r_3)) /\ (r_3 < tail)) -> ((Znth p_3 q_l_2 0) < (Znth r_3 q_l_2 0)))) (PreH22 : forall (p_4: Z) , forall (r_4: Z) , ((((head <= p_4) /\ (p_4 < r_4)) /\ (r_4 < tail)) -> ((Znth (Znth p_4 q_l_2 0) l 0) > (Znth (Znth r_4 q_l_2 0) l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))
.

Definition maxSlidingWindow_entail_wit_8 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> (((i - k_pre ) < (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < i)))) (PreH20 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH21 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full q_pre n_pre (replace_Znth (tail) (i) (q_l_2)) )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < (tail + 1 )) ” 
  &&  “ ((tail + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head (tail + 1 ) (i + 1 ) k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < (tail + 1 ))) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> (((i - k_pre ) < (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < i)))) (PreH20 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH21 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (((0 <= (Znth head (replace_Znth (tail) (i) (q_l_2)) 0)) /\ ((Znth head (replace_Znth (tail) (i) (q_l_2)) 0) < n_pre)) /\ ((0 <= (Znth ((tail + 1 ) - 1 ) (replace_Znth (tail) (i) (q_l_2)) 0)) /\ ((Znth ((tail + 1 ) - 1 ) (replace_Znth (tail) (i) (q_l_2)) 0) < n_pre))) ” 
  &&  “ (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1 ) (i + 1 ) k_pre ) ” 
  &&  “ ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_8_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> (((i - k_pre ) < (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < i)))) (PreH20 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH21 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (((0 <= (Znth head (replace_Znth (tail) (i) (q_l_2)) 0)) /\ ((Znth head (replace_Znth (tail) (i) (q_l_2)) 0) < n_pre)) /\ ((0 <= (Znth ((tail + 1 ) - 1 ) (replace_Znth (tail) (i) (q_l_2)) 0)) /\ ((Znth ((tail + 1 ) - 1 ) (replace_Znth (tail) (i) (q_l_2)) 0) < n_pre)))
.

Definition maxSlidingWindow_entail_wit_8_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> (((i - k_pre ) < (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < i)))) (PreH20 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH21 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1 ) (i + 1 ) k_pre )
.

Definition maxSlidingWindow_entail_wit_8_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH16 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH17 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) (PreH19 : forall (pos_3: Z) , (((head <= pos_3) /\ (pos_3 < tail)) -> (((i - k_pre ) < (Znth pos_3 q_l_2 0)) /\ ((Znth pos_3 q_l_2 0) < i)))) (PreH20 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l_2 0) < (Znth r q_l_2 0)))) (PreH21 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l_2 0) l 0) > (Znth (Znth r_2 q_l_2 0) l 0)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0)))) (PreH23 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre)
.

Definition maxSlidingWindow_entail_wit_9 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i >= (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH18 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH19 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (i + 1 )) ” 
  &&  “ (head < n_pre) ” 
  &&  “ (0 <= (Znth head q_l 0)) ” 
  &&  “ ((Znth head q_l 0) < n_pre) ” 
  &&  “ (out_idx = ((i - k_pre ) + 1 )) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx < ((n_pre - k_pre ) + 1 )) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i >= (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH18 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH19 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_9_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i >= (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH18 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH19 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) )
.

Definition maxSlidingWindow_entail_wit_10 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l_2 0))) (PreH13 : ((Znth head q_l_2 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH19 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH20 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) )) (PreH21 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.seg out_pre 0 (out_idx + 1 ) (app (out_l_2) ((cons ((Znth (Znth head q_l_2 0) l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (i + 1 )) ” 
  &&  “ (out_idx = ((i - k_pre ) + 1 )) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx < ((n_pre - k_pre ) + 1 )) ” 
  &&  “ (SWMOutputPrefix l k_pre (out_idx + 1 ) out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 (out_idx + 1 ) out_l )
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l_2 0))) (PreH13 : ((Znth head q_l_2 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH19 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH20 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) )) (PreH21 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (SWMOutputPrefix l k_pre (out_idx + 1 ) (app (out_l_2) ((cons ((Znth (Znth head q_l_2 0) l 0)) ((@nil Z))))) ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_10_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l_2 0))) (PreH13 : ((Znth head q_l_2 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH19 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH20 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) )) (PreH21 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (SWMOutputPrefix l k_pre (out_idx + 1 ) (app (out_l_2) ((cons ((Znth (Znth head q_l_2 0) l 0)) ((@nil Z))))) )
.

Definition maxSlidingWindow_entail_wit_11_1 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i < (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH18 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH19 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= (i + 1 )) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ (((i + 1 ) < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= (i + 1 )) -> (out_idx = (((i + 1 ) - k_pre ) + 1 ))) ” 
  &&  “ ((k_pre <= (i + 1 )) -> (head < tail)) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
.

Definition maxSlidingWindow_entail_wit_11_2 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (out_idx = ((i - k_pre ) + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH14 : (SWMOutputPrefix l k_pre (out_idx + 1 ) out_l_2 )) (PreH15 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH16 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH17 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 (out_idx + 1 ) out_l_2 )
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= (i + 1 )) ” 
  &&  “ (0 <= (out_idx + 1 )) ” 
  &&  “ ((out_idx + 1 ) <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ (((i + 1 ) < k_pre) -> ((out_idx + 1 ) = 0)) ” 
  &&  “ ((k_pre <= (i + 1 )) -> ((out_idx + 1 ) = (((i + 1 ) - k_pre ) + 1 ))) ” 
  &&  “ ((k_pre <= (i + 1 )) -> (head < tail)) ” 
  &&  “ (SWMOutputPrefix l k_pre (out_idx + 1 ) out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 (out_idx + 1 ) out_l )
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
.

Definition maxSlidingWindow_entail_wit_12 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : (((i + 1 ) < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= (i + 1 )) -> (out_idx = (((i + 1 ) - k_pre ) + 1 )))) (PreH15 : ((k_pre <= (i + 1 )) -> (head < tail))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH17 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH18 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> ((0 <= (Znth pos_2 q_l_2 0)) /\ ((Znth pos_2 q_l_2 0) < n_pre)))) (PreH19 : forall (idx_2: Z) , (((0 <= idx_2) /\ (idx_2 < n_pre)) -> (((-10000) <= (Znth idx_2 l 0)) /\ ((Znth idx_2 l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= (i + 1 )) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ (((i + 1 ) < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= (i + 1 )) -> (out_idx = (((i + 1 ) - k_pre ) + 1 ))) ” 
  &&  “ ((k_pre <= (i + 1 )) -> (head < tail)) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
.

Definition maxSlidingWindow_entail_wit_13 := 
(
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (out_l: (@list Z))  (q_l: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= n_pre) ” 
  &&  “ (out_idx = ((n_pre - k_pre ) + 1 )) ” 
  &&  “ (SlidingWindowMaximum l k_pre out_l ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full out_pre ((n_pre - k_pre ) + 1 ) out_l )
  **  (IntArray.full q_pre n_pre q_l )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  TT && emp 
|--
  “ (SlidingWindowMaximum l k_pre out_l_2 ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_13_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH18 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l_2 0)) /\ ((Znth pos q_l_2 0) < n_pre)))) (PreH20 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (SlidingWindowMaximum l k_pre out_l_2 )
.

Definition maxSlidingWindow_return_wit_1 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= head)) (PreH7 : (head <= tail)) (PreH8 : (tail <= n_pre)) (PreH9 : (out_idx = ((n_pre - k_pre ) + 1 ))) (PreH10 : (SlidingWindowMaximum l k_pre out_l_2 )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full out_pre ((n_pre - k_pre ) + 1 ) out_l_2 )
  **  (IntArray.full q_pre n_pre q_l_2 )
|--
  EX (q_l: (@list Z))  (out_l: (@list Z)) ,
  “ (SlidingWindowMaximum l k_pre out_l ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full out_pre ((n_pre - k_pre ) + 1 ) out_l )
  **  (IntArray.full q_pre n_pre q_l )
.

Definition maxSlidingWindow_partial_solve_wit_1 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH17 : (SWMQueueDropLoopState l q_l head tail i k_pre )) (PreH18 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH19 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH20 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH21 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH22 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ (head < tail) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueDropLoopState l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) <= (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (((q_pre + (head * sizeof(INT)))) # Int  |-> (Znth head q_l 0))
  **  (IntArray.missing_i q_pre head 0 n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
.

Definition maxSlidingWindow_partial_solve_wit_2 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH17 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH18 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH19 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ (head < tail) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (((q_pre + ((tail - 1 ) * sizeof(INT)))) # Int  |-> (Znth (tail - 1 ) q_l 0))
  **  (IntArray.missing_i q_pre (tail - 1 ) 0 n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
.

Definition maxSlidingWindow_partial_solve_wit_3 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH17 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH18 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH19 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full q_pre n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  “ (head < tail) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (((nums_pre + ((Znth (tail - 1 ) q_l 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (tail - 1 ) q_l 0) l 0))
  **  (IntArray.missing_i nums_pre (Znth (tail - 1 ) q_l 0) 0 n_pre l )
  **  (IntArray.full q_pre n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
.

Definition maxSlidingWindow_partial_solve_wit_4 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH17 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH18 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH19 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) (PreH20 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH21 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH22 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full q_pre n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  “ (head < tail) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 n_pre l )
  **  (IntArray.full q_pre n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
.

Definition maxSlidingWindow_partial_solve_wit_5 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= i)) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH16 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH17 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH18 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) (PreH19 : forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i)))) (PreH20 : forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0)))) (PreH21 : forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0)))) (PreH22 : ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l 0) l 0) > (Znth i l 0)))) (PreH23 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head <= tail) ” 
  &&  “ (tail <= i) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx <= ((n_pre - k_pre ) + 1 )) ” 
  &&  “ ((i < k_pre) -> (out_idx = 0)) ” 
  &&  “ ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 ))) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ” 
  &&  “ forall (pos_2: Z) , (((head <= pos_2) /\ (pos_2 < tail)) -> (((i - k_pre ) < (Znth pos_2 q_l 0)) /\ ((Znth pos_2 q_l 0) < i))) ” 
  &&  “ forall (p: Z) , forall (r: Z) , ((((head <= p) /\ (p < r)) /\ (r < tail)) -> ((Znth p q_l 0) < (Znth r q_l 0))) ” 
  &&  “ forall (p_2: Z) , forall (r_2: Z) , ((((head <= p_2) /\ (p_2 < r_2)) /\ (r_2 < tail)) -> ((Znth (Znth p_2 q_l 0) l 0) > (Znth (Znth r_2 q_l 0) l 0))) ” 
  &&  “ ((head < tail) -> ((Znth (Znth (tail - 1 ) q_l 0) l 0) > (Znth i l 0))) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (((q_pre + (tail * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i q_pre tail 0 n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
.

Definition maxSlidingWindow_partial_solve_wit_6 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l 0))) (PreH13 : ((Znth head q_l 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH18 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH20 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) )) (PreH21 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full q_pre n_pre q_l )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (i + 1 )) ” 
  &&  “ (head < n_pre) ” 
  &&  “ (0 <= (Znth head q_l 0)) ” 
  &&  “ ((Znth head q_l 0) < n_pre) ” 
  &&  “ (out_idx = ((i - k_pre ) + 1 )) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx < ((n_pre - k_pre ) + 1 )) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (((q_pre + (head * sizeof(INT)))) # Int  |-> (Znth head q_l 0))
  **  (IntArray.missing_i q_pre head 0 n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
.

Definition maxSlidingWindow_partial_solve_wit_7 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l 0))) (PreH13 : ((Znth head q_l 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH18 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH20 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) )) (PreH21 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full q_pre n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (i + 1 )) ” 
  &&  “ (head < n_pre) ” 
  &&  “ (0 <= (Znth head q_l 0)) ” 
  &&  “ ((Znth head q_l 0) < n_pre) ” 
  &&  “ (out_idx = ((i - k_pre ) + 1 )) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx < ((n_pre - k_pre ) + 1 )) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (((nums_pre + ((Znth head q_l 0) * sizeof(INT)))) # Int  |-> (Znth (Znth head q_l 0) l 0))
  **  (IntArray.missing_i nums_pre (Znth head q_l 0) 0 n_pre l )
  **  (IntArray.full q_pre n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
.

Definition maxSlidingWindow_partial_solve_wit_8 := 
forall (q_pre: Z) (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l 0))) (PreH13 : ((Znth head q_l 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH18 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH19 : forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre)))) (PreH20 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) )) (PreH21 : forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full q_pre n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
|--
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ ((Zlength (q_l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= head) ” 
  &&  “ (head < tail) ” 
  &&  “ (tail <= (i + 1 )) ” 
  &&  “ (head < n_pre) ” 
  &&  “ (0 <= (Znth head q_l 0)) ” 
  &&  “ ((Znth head q_l 0) < n_pre) ” 
  &&  “ (out_idx = ((i - k_pre ) + 1 )) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (out_idx < ((n_pre - k_pre ) + 1 )) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ forall (pos: Z) , (((head <= pos) /\ (pos < tail)) -> ((0 <= (Znth pos q_l 0)) /\ ((Znth pos q_l 0) < n_pre))) ” 
  &&  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) ) ” 
  &&  “ forall (idx: Z) , (((0 <= idx) /\ (idx < n_pre)) -> (((-10000) <= (Znth idx l 0)) /\ ((Znth idx l 0) <= 10000))) ”
  &&  (((out_pre + (out_idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full q_pre n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_maxSlidingWindow_safety_wit_1 : maxSlidingWindow_safety_wit_1.
Axiom proof_of_maxSlidingWindow_safety_wit_2 : maxSlidingWindow_safety_wit_2.
Axiom proof_of_maxSlidingWindow_safety_wit_3 : maxSlidingWindow_safety_wit_3.
Axiom proof_of_maxSlidingWindow_safety_wit_4 : maxSlidingWindow_safety_wit_4.
Axiom proof_of_maxSlidingWindow_safety_wit_5 : maxSlidingWindow_safety_wit_5.
Axiom proof_of_maxSlidingWindow_safety_wit_6 : maxSlidingWindow_safety_wit_6.
Axiom proof_of_maxSlidingWindow_safety_wit_7 : maxSlidingWindow_safety_wit_7.
Axiom proof_of_maxSlidingWindow_safety_wit_8 : maxSlidingWindow_safety_wit_8.
Axiom proof_of_maxSlidingWindow_safety_wit_9 : maxSlidingWindow_safety_wit_9.
Axiom proof_of_maxSlidingWindow_safety_wit_10 : maxSlidingWindow_safety_wit_10.
Axiom proof_of_maxSlidingWindow_safety_wit_11 : maxSlidingWindow_safety_wit_11.
Axiom proof_of_maxSlidingWindow_safety_wit_12 : maxSlidingWindow_safety_wit_12.
Axiom proof_of_maxSlidingWindow_safety_wit_13 : maxSlidingWindow_safety_wit_13.
Axiom proof_of_maxSlidingWindow_safety_wit_14 : maxSlidingWindow_safety_wit_14.
Axiom proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1.
Axiom proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2.
Axiom proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3.
Axiom proof_of_maxSlidingWindow_entail_wit_4_1 : maxSlidingWindow_entail_wit_4_1.
Axiom proof_of_maxSlidingWindow_entail_wit_4_2 : maxSlidingWindow_entail_wit_4_2.
Axiom proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5.
Axiom proof_of_maxSlidingWindow_entail_wit_6 : maxSlidingWindow_entail_wit_6.
Axiom proof_of_maxSlidingWindow_entail_wit_7_1 : maxSlidingWindow_entail_wit_7_1.
Axiom proof_of_maxSlidingWindow_entail_wit_7_2 : maxSlidingWindow_entail_wit_7_2.
Axiom proof_of_maxSlidingWindow_entail_wit_8 : maxSlidingWindow_entail_wit_8.
Axiom proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9.
Axiom proof_of_maxSlidingWindow_entail_wit_10 : maxSlidingWindow_entail_wit_10.
Axiom proof_of_maxSlidingWindow_entail_wit_11_1 : maxSlidingWindow_entail_wit_11_1.
Axiom proof_of_maxSlidingWindow_entail_wit_11_2 : maxSlidingWindow_entail_wit_11_2.
Axiom proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12.
Axiom proof_of_maxSlidingWindow_entail_wit_13 : maxSlidingWindow_entail_wit_13.
Axiom proof_of_maxSlidingWindow_return_wit_1 : maxSlidingWindow_return_wit_1.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_1 : maxSlidingWindow_partial_solve_wit_1.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_2 : maxSlidingWindow_partial_solve_wit_2.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_3 : maxSlidingWindow_partial_solve_wit_3.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_4 : maxSlidingWindow_partial_solve_wit_4.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_5 : maxSlidingWindow_partial_solve_wit_5.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_6 : maxSlidingWindow_partial_solve_wit_6.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_7 : maxSlidingWindow_partial_solve_wit_7.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_8 : maxSlidingWindow_partial_solve_wit_8.

End VC_Correct.
