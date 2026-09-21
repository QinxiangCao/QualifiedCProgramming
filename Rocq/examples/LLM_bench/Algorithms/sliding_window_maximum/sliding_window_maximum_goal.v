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

(*----- Function maxSlidingWindow -----*)

Definition maxSlidingWindow_safety_wit_1 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  ((( &( "z" ) )) # Int  |->_)
  **  (IntArray.undef_full ( &( "q" ) ) 100000 )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_2 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (q_init: (@list Z)) (z: Z) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 z q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) z n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_3 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (q_init: (@list Z)) (z: Z) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (IntArray.seg ( &( "q" ) ) 0 (z + 1 ) (app (q_init) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "q" ) ) (z + 1 ) n_pre )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "z" ) )) # Int  |-> z)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((z + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (z + 1 )) ”
.

Definition maxSlidingWindow_safety_wit_4 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (q_init: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "head" ) )) # Int  |->_)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 z q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) z n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_5 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (q_init: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "tail" ) )) # Int  |->_)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 z q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) z n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_6 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (q_init: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "out_idx" ) )) # Int  |->_)
  **  ((( &( "tail" ) )) # Int  |-> 0)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 z q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) z n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_7 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (q_init: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out_idx" ) )) # Int  |-> 0)
  **  ((( &( "tail" ) )) # Int  |-> 0)
  **  ((( &( "head" ) )) # Int  |-> 0)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 z q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) z n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition maxSlidingWindow_safety_wit_8 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueueDropLoopState l q_l head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) ,
  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((i - k_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - k_pre )) ”
.

Definition maxSlidingWindow_safety_wit_9 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : ((Znth head q_l 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH21 : (SWMQueueDropLoopState l q_l head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) ,
  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((head + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (head + 1 )) ”
.

Definition maxSlidingWindow_safety_wit_10 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((tail - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail - 1 )) ”
.

Definition maxSlidingWindow_safety_wit_11 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition maxSlidingWindow_safety_wit_12 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH21 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((tail - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail - 1 )) ”
.

Definition maxSlidingWindow_safety_wit_13 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  (IntArray.full ( &( "q" ) ) n_pre (replace_Znth (tail) (i) (q_l)) )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((tail + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail + 1 )) ”
.

Definition maxSlidingWindow_safety_wit_14 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH21 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  (IntArray.full ( &( "q" ) ) n_pre (replace_Znth (tail) (i) (q_l)) )
  **  (IntArray.full nums_pre n_pre l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((tail + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (tail + 1 )) ”
.

Definition maxSlidingWindow_safety_wit_15 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) (PreH17 : ((Zlength (out_l)) = out_idx)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH19 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH20 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH21 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((k_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k_pre - 1 )) ”
.

Definition maxSlidingWindow_safety_wit_16 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : ((i < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH15 : (Forall (Z.le ((-10000))) l )) (PreH16 : (Forall (Z.ge (10000)) l )) (PreH17 : ((Zlength (out_l)) = out_idx)) (PreH18 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH19 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH20 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH21 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition maxSlidingWindow_safety_wit_17 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l 0))) (PreH13 : ((Znth head q_l 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH21 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH24 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) )) ,
  (IntArray.seg out_pre 0 (out_idx + 1 ) (app (out_l) ((cons ((Znth (Znth head q_l 0) l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((out_idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_idx + 1 )) ”
.

Definition maxSlidingWindow_safety_wit_18 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : (((i + 1 ) < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= (i + 1 )) -> (out_idx = (((i + 1 ) - k_pre ) + 1 )))) (PreH15 : ((k_pre <= (i + 1 )) -> (head < tail))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) ,
  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "head" ) )) # Int  |-> head)
  **  ((( &( "tail" ) )) # Int  |-> tail)
  **  ((( &( "out_idx" ) )) # Int  |-> out_idx)
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition maxSlidingWindow_entail_wit_1 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.undef_full ( &( "q" ) ) 100000 )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
|--
  EX (q_init: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (q_init)) = 0) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 0 q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.undef_full ( &( "q" ) ) 100000 )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
  &&  (IntArray.undef_seg ( &( "q" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
).

Definition maxSlidingWindow_entail_wit_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.undef_full ( &( "q" ) ) 100000 )
|--
  “ ((Zlength ((@nil Z))) = 0) ”
.

Definition maxSlidingWindow_entail_wit_1_split_goal_spatial := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall (Z.le ((-10000))) l )) (PreH6 : (Forall (Z.ge (10000)) l )) ,
  (IntArray.undef_full ( &( "q" ) ) 100000 )
|--
  (IntArray.undef_seg ( &( "q" ) ) 0 n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_entail_wit_2 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (q_init_2: (@list Z)) (z: Z) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init_2)) = z)) ,
  (IntArray.seg ( &( "q" ) ) 0 (z + 1 ) (app (q_init_2) ((cons (0) ((@nil Z))))) )
  **  (IntArray.undef_seg ( &( "q" ) ) (z + 1 ) n_pre )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  EX (q_init: (@list Z)) ,
  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ (0 <= (z + 1 )) ” 
  &&  “ ((z + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (q_init)) = (z + 1 )) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 (z + 1 ) q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) (z + 1 ) n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (q_init_2: (@list Z)) (z: Z) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init_2)) = z)) ,
  TT && emp 
|--
  “ ((Zlength ((app (q_init_2) ((cons (0) ((@nil Z))))))) = (z + 1 )) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (q_init_2: (@list Z)) (z: Z) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init_2)) = z)) ,
  ((Zlength ((app (q_init_2) ((cons (0) ((@nil Z))))))) = (z + 1 ))
.

Definition maxSlidingWindow_entail_wit_3 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (q_init: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 z q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) z n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ (SWMOutputPrefix l k_pre 0 out_l ) ” 
  &&  “ (SWMQueueState l q_l 0 0 0 k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (0) (0) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (0) (0) (q_l)) ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 0 out_l )
  **  (IntArray.undef_seg out_pre 0 ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (q_init: (@list Z)) (z: Z) (PreH1 : (z >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (IntArray.seg ( &( "q" ) ) 0 z q_init )
|--
  EX (q_l: (@list Z)) ,
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (SWMOutputPrefix l k_pre 0 (@nil Z) ) ” 
  &&  “ (SWMQueueState l q_l 0 0 0 k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (0) (0) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (0) (0) (q_l)) ) ”
  &&  (IntArray.full ( &( "q" ) ) n_pre q_l )
).

Definition maxSlidingWindow_entail_wit_4 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l_2 )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueDropLoopState l q_l head tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  TT && emp 
|--
  “ (SWMQueueDropLoopState l q_l_2 head tail i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_4_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (SWMQueueDropLoopState l q_l_2 head tail i k_pre )
.

Definition maxSlidingWindow_entail_wit_5 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (IntArray.full ( &( "q" ) ) n_pre q_l_2 )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueDropLoopState l q_l (head + 1 ) tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist ((head + 1 )) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist ((head + 1 )) (tail) (q_l)) ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  TT && emp 
|--
  “ (Forall (Z.gt (n_pre)) (sublist ((head + 1 )) (tail) (q_l_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (sublist ((head + 1 )) (tail) (q_l_2)) ) ” 
  &&  “ (SWMQueueDropLoopState l q_l_2 (head + 1 ) tail i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_5_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (Forall (Z.gt (n_pre)) (sublist ((head + 1 )) (tail) (q_l_2)) )
.

Definition maxSlidingWindow_entail_wit_5_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (Forall (Z.le (0)) (sublist ((head + 1 )) (tail) (q_l_2)) )
.

Definition maxSlidingWindow_entail_wit_5_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) <= (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (SWMQueueDropLoopState l q_l_2 (head + 1 ) tail i k_pre )
.

Definition maxSlidingWindow_entail_wit_6_1 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l_2 )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  TT && emp 
|--
  “ (SWMQueuePendingState l q_l_2 head tail i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_6_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (SWMQueuePendingState l q_l_2 head tail i k_pre )
.

Definition maxSlidingWindow_entail_wit_6_2 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (IntArray.full ( &( "q" ) ) n_pre q_l_2 )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  TT && emp 
|--
  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre))) ” 
  &&  “ (SWMQueuePendingState l q_l_2 head tail i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_6_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))
.

Definition maxSlidingWindow_entail_wit_6_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth head q_l_2 0) > (i - k_pre ))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueDropLoopState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (SWMQueuePendingState l q_l_2 head tail i k_pre )
.

Definition maxSlidingWindow_entail_wit_7 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l_2 )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head (tail - 1 ) i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) ((tail - 1 )) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) ((tail - 1 )) (q_l)) ) ” 
  &&  “ ((head < (tail - 1 )) -> ((((0 <= ((tail - 1 ) - 1 )) /\ (((tail - 1 ) - 1 ) < n_pre)) /\ (0 <= (Znth ((tail - 1 ) - 1 ) q_l 0))) /\ ((Znth ((tail - 1 ) - 1 ) q_l 0) < n_pre))) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  TT && emp 
|--
  “ ((head < (tail - 1 )) -> ((((0 <= ((tail - 1 ) - 1 )) /\ (((tail - 1 ) - 1 ) < n_pre)) /\ (0 <= (Znth ((tail - 1 ) - 1 ) q_l_2 0))) /\ ((Znth ((tail - 1 ) - 1 ) q_l_2 0) < n_pre))) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) ((tail - 1 )) (q_l_2)) ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) ((tail - 1 )) (q_l_2)) ) ” 
  &&  “ (SWMQueuePendingState l q_l_2 head (tail - 1 ) i k_pre ) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_7_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  ((head < (tail - 1 )) -> ((((0 <= ((tail - 1 ) - 1 )) /\ (((tail - 1 ) - 1 ) < n_pre)) /\ (0 <= (Znth ((tail - 1 ) - 1 ) q_l_2 0))) /\ ((Znth ((tail - 1 ) - 1 ) q_l_2 0) < n_pre)))
.

Definition maxSlidingWindow_entail_wit_7_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (Forall (Z.gt (n_pre)) (sublist (head) ((tail - 1 )) (q_l_2)) )
.

Definition maxSlidingWindow_entail_wit_7_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (Forall (Z.le (0)) (sublist (head) ((tail - 1 )) (q_l_2)) )
.

Definition maxSlidingWindow_entail_wit_7_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) <= (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (SWMQueuePendingState l q_l_2 head (tail - 1 ) i k_pre )
.

Definition maxSlidingWindow_entail_wit_8_1 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (IntArray.full ( &( "q" ) ) n_pre (replace_Znth (tail) (i) (q_l_2)) )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head (tail + 1 ) (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) ((tail + 1 )) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) ((tail + 1 )) (q_l)) ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  TT && emp 
|--
  “ (Forall (Z.gt (n_pre)) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (i) (q_l_2)))) ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (i) (q_l_2)))) ) ” 
  &&  “ (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1 ) (i + 1 ) k_pre ) ” 
  &&  “ ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_8_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (Forall (Z.gt (n_pre)) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (i) (q_l_2)))) )
.

Definition maxSlidingWindow_entail_wit_8_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (Forall (Z.le (0)) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (i) (q_l_2)))) )
.

Definition maxSlidingWindow_entail_wit_8_1_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1 ) (i + 1 ) k_pre )
.

Definition maxSlidingWindow_entail_wit_8_1_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre)
.

Definition maxSlidingWindow_entail_wit_8_2 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (IntArray.full ( &( "q" ) ) n_pre (replace_Znth (tail) (i) (q_l_2)) )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head (tail + 1 ) (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) ((tail + 1 )) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) ((tail + 1 )) (q_l)) ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  TT && emp 
|--
  “ (Forall (Z.gt (n_pre)) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (i) (q_l_2)))) ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (i) (q_l_2)))) ) ” 
  &&  “ (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1 ) (i + 1 ) k_pre ) ” 
  &&  “ ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_8_2_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (Forall (Z.gt (n_pre)) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (i) (q_l_2)))) )
.

Definition maxSlidingWindow_entail_wit_8_2_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (Forall (Z.le (0)) (sublist (head) ((tail + 1 )) ((replace_Znth (tail) (i) (q_l_2)))) )
.

Definition maxSlidingWindow_entail_wit_8_2_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  (SWMQueueState l (replace_Znth (tail) (i) (q_l_2)) head (tail + 1 ) (i + 1 ) k_pre )
.

Definition maxSlidingWindow_entail_wit_8_2_split_goal_4 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l_2: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l_2 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l_2)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueuePendingState l q_l_2 head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l_2 0))) /\ ((Znth (tail - 1 ) q_l_2 0) < n_pre)))) ,
  ((Zlength ((replace_Znth (tail) (i) (q_l_2)))) = n_pre)
.

Definition maxSlidingWindow_entail_wit_9 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i >= (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l_2 )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i >= (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  TT && emp 
|--
  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) ) ” 
  &&  “ ((Znth head q_l_2 0) < n_pre) ” 
  &&  “ (0 <= (Znth head q_l_2 0)) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_9_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i >= (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) )
.

Definition maxSlidingWindow_entail_wit_9_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i >= (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  ((Znth head q_l_2 0) < n_pre)
.

Definition maxSlidingWindow_entail_wit_9_split_goal_3 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i >= (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (0 <= (Znth head q_l_2 0))
.

Definition maxSlidingWindow_entail_wit_10_1 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l_2 0))) (PreH13 : ((Znth head q_l_2 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) )) ,
  (IntArray.seg out_pre 0 (out_idx + 1 ) (app (out_l_2) ((cons ((Znth (Znth head q_l_2 0) l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l_2 )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = (out_idx + 1 )) ” 
  &&  “ (SWMOutputPrefix l k_pre (out_idx + 1 ) out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 (out_idx + 1 ) out_l )
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
) \/
(
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l_2 0))) (PreH13 : ((Znth head q_l_2 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) )) ,
  TT && emp 
|--
  “ (SWMOutputPrefix l k_pre (((i - k_pre ) + 1 ) + 1 ) (app (out_l_2) ((cons ((Znth (Znth head q_l_2 0) l 0)) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (out_l_2) ((cons ((Znth (Znth head q_l_2 0) l 0)) ((@nil Z))))))) = (((i - k_pre ) + 1 ) + 1 )) ”
  &&  emp
).

Definition maxSlidingWindow_entail_wit_10_1_split_goal_1 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l_2 0))) (PreH13 : ((Znth head q_l_2 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) )) ,
  (SWMOutputPrefix l k_pre (((i - k_pre ) + 1 ) + 1 ) (app (out_l_2) ((cons ((Znth (Znth head q_l_2 0) l 0)) ((@nil Z))))) )
.

Definition maxSlidingWindow_entail_wit_10_1_split_goal_2 := 
forall (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l_2 0))) (PreH13 : ((Znth head q_l_2 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) (PreH24 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l_2 0) l 0) )) ,
  ((Zlength ((app (out_l_2) ((cons ((Znth (Znth head q_l_2 0) l 0)) ((@nil Z))))))) = (((i - k_pre ) + 1 ) + 1 ))
.

Definition maxSlidingWindow_entail_wit_10_2 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (i < (k_pre - 1 ))) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l_2)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head < tail)) (PreH11 : (tail <= (i + 1 ))) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l_2 )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_entail_wit_11 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (q_l_2: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l_2)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head <= tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (0 <= out_idx)) (PreH12 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH13 : (((i + 1 ) < k_pre) -> (out_idx = 0))) (PreH14 : ((k_pre <= (i + 1 )) -> (out_idx = (((i + 1 ) - k_pre ) + 1 )))) (PreH15 : ((k_pre <= (i + 1 )) -> (head < tail))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l_2)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH20 : (SWMQueueState l q_l_2 head tail (i + 1 ) k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l_2)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l_2)) )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l_2 )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_entail_wit_12 := 
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueState l q_l head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= head) ” 
  &&  “ (0 <= tail) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (SlidingWindowMaximum l k_pre out_l ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full out_pre ((n_pre - k_pre ) + 1 ) out_l )
  **  (IntArray.undef_full ( &( "q" ) ) 100000 )
) \/
(
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : ((k_pre <= i) -> (head < tail))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l_2)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l_2 )) (PreH21 : (SWMQueueState l q_l head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) ,
  (IntArray.seg out_pre 0 out_idx out_l_2 )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= head) ” 
  &&  “ (0 <= tail) ” 
  &&  “ (0 <= out_idx) ” 
  &&  “ (SlidingWindowMaximum l k_pre out_l ) ”
  &&  (IntArray.full out_pre ((n_pre - k_pre ) + 1 ) out_l )
  **  (IntArray.undef_full ( &( "q" ) ) 100000 )
).

Definition maxSlidingWindow_return_wit_1 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l_2: (@list Z)) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (0 <= head)) (PreH2 : (0 <= tail)) (PreH3 : (0 <= out_idx)) (PreH4 : (SlidingWindowMaximum l k_pre out_l_2 )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full out_pre ((n_pre - k_pre ) + 1 ) out_l_2 )
|--
  EX (out_l: (@list Z)) ,
  “ (SlidingWindowMaximum l k_pre out_l ) ”
  &&  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full out_pre ((n_pre - k_pre ) + 1 ) out_l )
.

Definition maxSlidingWindow_partial_solve_wit_1 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (q_init: (@list Z)) (z: Z) (PreH1 : (z < n_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : (Forall (Z.le ((-10000))) l )) (PreH7 : (Forall (Z.ge (10000)) l )) (PreH8 : (0 <= z)) (PreH9 : (z <= n_pre)) (PreH10 : ((Zlength (q_init)) = z)) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 z q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) z n_pre )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ (z < n_pre) ” 
  &&  “ (1 <= k_pre) ” 
  &&  “ (k_pre <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ (0 <= z) ” 
  &&  “ (z <= n_pre) ” 
  &&  “ ((Zlength (q_init)) = z) ”
  &&  (((( &( "q" ) ) + (z * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg ( &( "q" ) ) (z + 1 ) n_pre )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.undef_full out_pre ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.seg ( &( "q" ) ) 0 z q_init )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_partial_solve_wit_2 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueueDropLoopState l q_l head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueDropLoopState l q_l head tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ”
  &&  (((( &( "q" ) ) + (head * sizeof(INT)))) # Int  |-> (Znth head q_l 0))
  **  (IntArray.missing_i ( &( "q" ) ) head 0 n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_partial_solve_wit_3 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ”
  &&  (((( &( "q" ) ) + ((tail - 1 ) * sizeof(INT)))) # Int  |-> (Znth (tail - 1 ) q_l 0))
  **  (IntArray.missing_i ( &( "q" ) ) (tail - 1 ) 0 n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_partial_solve_wit_4 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ”
  &&  (((nums_pre + ((Znth (tail - 1 ) q_l 0) * sizeof(INT)))) # Int  |-> (Znth (Znth (tail - 1 ) q_l 0) l 0))
  **  (IntArray.missing_i nums_pre (Znth (tail - 1 ) q_l 0) 0 n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_partial_solve_wit_5 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head < tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i nums_pre i 0 n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_partial_solve_wit_6 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : (head >= tail)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : ((Zlength (l)) = n_pre)) (PreH6 : ((Zlength (q_l)) = n_pre)) (PreH7 : (0 <= i)) (PreH8 : (i < n_pre)) (PreH9 : (0 <= head)) (PreH10 : (head <= tail)) (PreH11 : (tail <= i)) (PreH12 : (0 <= out_idx)) (PreH13 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH14 : ((i < k_pre) -> (out_idx = 0))) (PreH15 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH16 : (Forall (Z.le ((-10000))) l )) (PreH17 : (Forall (Z.ge (10000)) l )) (PreH18 : ((Zlength (out_l)) = out_idx)) (PreH19 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH20 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH21 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH22 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH23 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ (head >= tail) ” 
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ”
  &&  (((( &( "q" ) ) + (tail * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "q" ) ) tail 0 n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_partial_solve_wit_7 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (out_idx: Z) (tail: Z) (head: Z) (i: Z) (q_l: (@list Z)) (PreH1 : ((Znth (Znth (tail - 1 ) q_l 0) l 0) > (Znth i l 0))) (PreH2 : (head < tail)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : ((Zlength (l)) = n_pre)) (PreH7 : ((Zlength (q_l)) = n_pre)) (PreH8 : (0 <= i)) (PreH9 : (i < n_pre)) (PreH10 : (0 <= head)) (PreH11 : (head <= tail)) (PreH12 : (tail <= i)) (PreH13 : (0 <= out_idx)) (PreH14 : (out_idx <= ((n_pre - k_pre ) + 1 ))) (PreH15 : ((i < k_pre) -> (out_idx = 0))) (PreH16 : ((k_pre <= i) -> (out_idx = ((i - k_pre ) + 1 )))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH21 : (SWMQueuePendingState l q_l head tail i k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH24 : ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre)))) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
|--
  “ ((Znth (Znth (tail - 1 ) q_l 0) l 0) > (Znth i l 0)) ” 
  &&  “ (head < tail) ” 
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueuePendingState l q_l head tail i k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ ((head < tail) -> ((((0 <= (tail - 1 )) /\ ((tail - 1 ) < n_pre)) /\ (0 <= (Znth (tail - 1 ) q_l 0))) /\ ((Znth (tail - 1 ) q_l 0) < n_pre))) ”
  &&  (((( &( "q" ) ) + (tail * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "q" ) ) tail 0 n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_partial_solve_wit_8 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l 0))) (PreH13 : ((Znth head q_l 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH21 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH24 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) ) ”
  &&  (((( &( "q" ) ) + (head * sizeof(INT)))) # Int  |-> (Znth head q_l 0))
  **  (IntArray.missing_i ( &( "q" ) ) head 0 n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_partial_solve_wit_9 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l 0))) (PreH13 : ((Znth head q_l 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH21 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH24 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) )) ,
  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) ) ”
  &&  (((nums_pre + ((Znth head q_l 0) * sizeof(INT)))) # Int  |-> (Znth (Znth head q_l 0) l 0))
  **  (IntArray.missing_i nums_pre (Znth head q_l 0) 0 n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Definition maxSlidingWindow_partial_solve_wit_10 := 
forall (out_pre: Z) (k_pre: Z) (n_pre: Z) (nums_pre: Z) (l: (@list Z)) (out_l: (@list Z)) (q_l: (@list Z)) (i: Z) (head: Z) (tail: Z) (out_idx: Z) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : ((Zlength (q_l)) = n_pre)) (PreH6 : (0 <= i)) (PreH7 : (i < n_pre)) (PreH8 : (0 <= head)) (PreH9 : (head < tail)) (PreH10 : (tail <= (i + 1 ))) (PreH11 : (head < n_pre)) (PreH12 : (0 <= (Znth head q_l 0))) (PreH13 : ((Znth head q_l 0) < n_pre)) (PreH14 : (out_idx = ((i - k_pre ) + 1 ))) (PreH15 : (0 <= out_idx)) (PreH16 : (out_idx < ((n_pre - k_pre ) + 1 ))) (PreH17 : (Forall (Z.le ((-10000))) l )) (PreH18 : (Forall (Z.ge (10000)) l )) (PreH19 : ((Zlength (out_l)) = out_idx)) (PreH20 : (SWMOutputPrefix l k_pre out_idx out_l )) (PreH21 : (SWMQueueState l q_l head tail (i + 1 ) k_pre )) (PreH22 : (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) )) (PreH23 : (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) )) (PreH24 : (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) )) ,
  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg out_pre out_idx ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
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
  &&  “ (Forall (Z.le ((-10000))) l ) ” 
  &&  “ (Forall (Z.ge (10000)) l ) ” 
  &&  “ ((Zlength (out_l)) = out_idx) ” 
  &&  “ (SWMOutputPrefix l k_pre out_idx out_l ) ” 
  &&  “ (SWMQueueState l q_l head tail (i + 1 ) k_pre ) ” 
  &&  “ (Forall (Z.le (0)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (Forall (Z.gt (n_pre)) (sublist (head) (tail) (q_l)) ) ” 
  &&  “ (WindowMaxValue l ((i - k_pre ) + 1 ) (i + 1 ) (Znth (Znth head q_l 0) l 0) ) ”
  &&  (((out_pre + (out_idx * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre (out_idx + 1 ) ((n_pre - k_pre ) + 1 ) )
  **  (IntArray.full nums_pre n_pre l )
  **  (IntArray.full ( &( "q" ) ) n_pre q_l )
  **  (IntArray.seg out_pre 0 out_idx out_l )
  **  (IntArray.undef_seg ( &( "q" ) ) n_pre 100000 )
.

Module Type VC_Correct.


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
Axiom proof_of_maxSlidingWindow_safety_wit_15 : maxSlidingWindow_safety_wit_15.
Axiom proof_of_maxSlidingWindow_safety_wit_16 : maxSlidingWindow_safety_wit_16.
Axiom proof_of_maxSlidingWindow_safety_wit_17 : maxSlidingWindow_safety_wit_17.
Axiom proof_of_maxSlidingWindow_safety_wit_18 : maxSlidingWindow_safety_wit_18.
Axiom proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1.
Axiom proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2.
Axiom proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3.
Axiom proof_of_maxSlidingWindow_entail_wit_4 : maxSlidingWindow_entail_wit_4.
Axiom proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5.
Axiom proof_of_maxSlidingWindow_entail_wit_6_1 : maxSlidingWindow_entail_wit_6_1.
Axiom proof_of_maxSlidingWindow_entail_wit_6_2 : maxSlidingWindow_entail_wit_6_2.
Axiom proof_of_maxSlidingWindow_entail_wit_7 : maxSlidingWindow_entail_wit_7.
Axiom proof_of_maxSlidingWindow_entail_wit_8_1 : maxSlidingWindow_entail_wit_8_1.
Axiom proof_of_maxSlidingWindow_entail_wit_8_2 : maxSlidingWindow_entail_wit_8_2.
Axiom proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9.
Axiom proof_of_maxSlidingWindow_entail_wit_10_1 : maxSlidingWindow_entail_wit_10_1.
Axiom proof_of_maxSlidingWindow_entail_wit_10_2 : maxSlidingWindow_entail_wit_10_2.
Axiom proof_of_maxSlidingWindow_entail_wit_11 : maxSlidingWindow_entail_wit_11.
Axiom proof_of_maxSlidingWindow_entail_wit_12 : maxSlidingWindow_entail_wit_12.
Axiom proof_of_maxSlidingWindow_return_wit_1 : maxSlidingWindow_return_wit_1.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_1 : maxSlidingWindow_partial_solve_wit_1.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_2 : maxSlidingWindow_partial_solve_wit_2.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_3 : maxSlidingWindow_partial_solve_wit_3.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_4 : maxSlidingWindow_partial_solve_wit_4.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_5 : maxSlidingWindow_partial_solve_wit_5.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_6 : maxSlidingWindow_partial_solve_wit_6.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_7 : maxSlidingWindow_partial_solve_wit_7.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_8 : maxSlidingWindow_partial_solve_wit_8.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_9 : maxSlidingWindow_partial_solve_wit_9.
Axiom proof_of_maxSlidingWindow_partial_solve_wit_10 : maxSlidingWindow_partial_solve_wit_10.

End VC_Correct.
