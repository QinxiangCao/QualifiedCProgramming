From SimpleC.Verification Require Import VCPrelude.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P031_1194C_from_s_to_t_lib.
Local Open Scope sac.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function solver -----*)

Definition solver_safety_wit_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  ((( &( "j" ) )) # Int  |->_)
  **  (IntArray.full ( &( "cnt" ) ) 26 (repeat_Z (0) (26)) )
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i < (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH20 : (97 <= (Znth i source 0))) (PreH21 : ((Znth i source 0) <= 122)) (PreH22 : (GreedyPrefixMatch source target j i )) (PreH23 : (CountState source pool target 0 0 0 counts )) (PreH24 : (NonnegativeCounts counts )) (PreH25 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_4 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_5 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_6 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts )) (PreH20 : (NonnegativeCounts counts )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_7 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i < (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH20 : (97 <= (Znth i source 0))) (PreH21 : ((Znth i source 0) <= 122)) (PreH22 : (GreedyPrefixMatch source target j i )) (PreH23 : (CountState source pool target 0 0 0 counts )) (PreH24 : (NonnegativeCounts counts )) (PreH25 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH26 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_8 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_9 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength (source)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (0 <= j)) (PreH14 : (j <= (Zlength (target)))) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (source)))) (PreH17 : (j < (Zlength (target)))) (PreH18 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH19 : (97 <= (Znth j target 0))) (PreH20 : ((Znth j target 0) <= 122)) (PreH21 : (i < (Zlength (source)))) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH23 : (97 <= (Znth i source 0))) (PreH24 : ((Znth i source 0) <= 122)) (PreH25 : (GreedyPrefixMatch source target j i )) (PreH26 : (CountState source pool target 0 0 0 counts )) (PreH27 : (NonnegativeCounts counts )) (PreH28 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH29 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_10 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength (source)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (0 <= j)) (PreH14 : (j <= (Zlength (target)))) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (source)))) (PreH17 : (j < (Zlength (target)))) (PreH18 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH19 : (97 <= (Znth j target 0))) (PreH20 : ((Znth j target 0) <= 122)) (PreH21 : (i < (Zlength (source)))) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH23 : (97 <= (Znth i source 0))) (PreH24 : ((Znth i source 0) <= 122)) (PreH25 : (GreedyPrefixMatch source target j i )) (PreH26 : (CountState source pool target 0 0 0 counts )) (PreH27 : (NonnegativeCounts counts )) (PreH28 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH29 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_11 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength (source)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (0 <= j)) (PreH14 : (j <= (Zlength (target)))) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (source)))) (PreH17 : (j < (Zlength (target)))) (PreH18 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH19 : (97 <= (Znth j target 0))) (PreH20 : ((Znth j target 0) <= 122)) (PreH21 : (i < (Zlength (source)))) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH23 : (97 <= (Znth i source 0))) (PreH24 : ((Znth i source 0) <= 122)) (PreH25 : (GreedyPrefixMatch source target j i )) (PreH26 : (CountState source pool target 0 0 0 counts )) (PreH27 : (NonnegativeCounts counts )) (PreH28 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH29 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_12 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ ((j + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition solver_safety_wit_13 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_14 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts )) (PreH20 : (NonnegativeCounts counts )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_15 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength (source)))) (PreH3 : (NoSubsequence source target )) (PreH4 : (CountState source pool target 0 0 0 counts )) (PreH5 : (NonnegativeCounts counts )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_16 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (i = (Zlength (source)))) (PreH11 : (IsSubsequence source target )) (PreH12 : (CountState source pool target 0 0 0 counts )) (PreH13 : (NonnegativeCounts counts )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_17 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i < (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH15 : (97 <= (Znth i source 0))) (PreH16 : ((Znth i source 0) <= 122)) (PreH17 : (CountState source pool target i 0 0 counts )) (PreH18 : (NonnegativeCounts counts )) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_18 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts )) (PreH16 : (NonnegativeCounts counts )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_19 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_20 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 )) ”
.

Definition solver_safety_wit_21 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_22 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 )) ”
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 )) ”
).

Definition solver_safety_wit_22_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_22_split_goal_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ ((INT_MIN) <= ((Znth ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 )) ”
.

Definition solver_safety_wit_23 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts )) (PreH16 : (NonnegativeCounts counts )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_24 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i < (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH15 : (97 <= (Znth i pool 0))) (PreH16 : ((Znth i pool 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH18 : (NonnegativeCounts counts )) (PreH19 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_25 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH16 : (NonnegativeCounts counts )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_26 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 )) (counts)) )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_27 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 )) ”
.

Definition solver_safety_wit_28 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_29 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 )) ”
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 )) ”
).

Definition solver_safety_wit_29_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_29_split_goal_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ ((INT_MIN) <= ((Znth ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) + 1 )) ”
.

Definition solver_safety_wit_30 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH16 : (NonnegativeCounts counts )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_31 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i < (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH15 : (97 <= (Znth i target 0))) (PreH16 : ((Znth i target 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH18 : (NonnegativeCounts counts )) (PreH19 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_32 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i = (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH16 : (NonnegativeCounts counts )) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ False ”
.

Definition solver_safety_wit_33 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) ”
.

Definition solver_safety_wit_34 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_35 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) ”
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) ”
).

Definition solver_safety_wit_35_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 ) <= INT_MAX) ”
.

Definition solver_safety_wit_35_split_goal_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ ((INT_MIN) <= ((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) ”
.

Definition solver_safety_wit_36 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) ”
.

Definition solver_safety_wit_37 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_38 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_safety_wit_39 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) ”
.

Definition solver_safety_wit_40 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (97 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 97) ”
.

Definition solver_safety_wit_41 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_42 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (IsSubsequence source target )) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength (target)))) (PreH4 : (CountState source pool target (Zlength (source)) (Zlength (pool)) (i + 1 ) counts )) (PreH5 : (SupplyShortage source pool target )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition solver_safety_wit_43 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) 0) >= 0)) (PreH2 : (97 <= (Znth i target 0))) (PreH3 : ((Znth i target 0) <= 122)) (PreH4 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 100)) (PreH7 : (1 <= (Zlength (target)))) (PreH8 : ((Zlength (target)) <= 100)) (PreH9 : (1 <= (Zlength (pool)))) (PreH10 : ((Zlength (pool)) <= 100)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH14 : (IsSubsequence source target )) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (target)))) (PreH17 : (i < (Zlength (target)))) (PreH18 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH19 : (97 <= (Znth i target 0))) (PreH20 : ((Znth i target 0) <= 122)) (PreH21 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition solver_safety_wit_44 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i = (Zlength (target)))) (PreH2 : (IsSubsequence source target )) (PreH3 : (CountState source pool target (Zlength (source)) (Zlength (pool)) (Zlength (target)) counts )) (PreH4 : (NonnegativeCounts counts )) (PreH5 : (CanInsertFromPool source pool target )),
  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "t" ) )) # Ptr  |-> t_pre)
  **  ((( &( "p" ) )) # Ptr  |-> p_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition solver_entail_wit_1 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  (IntArray.full ( &( "cnt" ) ) 26 (repeat_Z (0) (26)) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (target))) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (source))) ”
  &&  “ (0 < (Zlength (target))) ”
  &&  “ ((Znth 0 (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth 0 target 0)) ”
  &&  “ (97 <= (Znth 0 target 0)) ”
  &&  “ ((Znth 0 target 0) <= 122) ”
  &&  “ (0 < (Zlength (source))) ”
  &&  “ ((Znth 0 (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth 0 source 0)) ”
  &&  “ (97 <= (Znth 0 source 0)) ”
  &&  “ ((Znth 0 source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target 0 0 ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  TT && emp 
|--
  “ (NonnegativeCounts (repeat_Z (0) (26)) ) ”
  &&  “ (CountState source pool target 0 0 0 (repeat_Z (0) (26)) ) ”
  &&  “ (GreedyPrefixMatch source target 0 0 ) ”
  &&  “ ((Znth 0 (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth 0 source 0)) ”
  &&  “ ((Znth 0 (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth 0 target 0)) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_1_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  (NonnegativeCounts (repeat_Z (0) (26)) )
.

Definition solver_entail_wit_1_split_goal_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  (CountState source pool target 0 0 0 (repeat_Z (0) (26)) )
.

Definition solver_entail_wit_1_split_goal_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  (GreedyPrefixMatch source target 0 0 )
.

Definition solver_entail_wit_1_split_goal_4 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  ((Znth 0 (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth 0 source 0))
.

Definition solver_entail_wit_1_split_goal_5 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  ((Znth 0 (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth 0 target 0))
.

Definition solver_entail_wit_1_split_goal_6 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))
.

Definition solver_entail_wit_1_split_goal_7 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))
.

Definition solver_entail_wit_1_split_goal_8 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (idx: Z), (((0 <= idx) /\ (idx < (Zlength (source)))) -> ((97 <= (Znth idx source 0)) /\ ((Znth idx source 0) <= 122)))) (PreH8 : forall (idx_2: Z), (((0 <= idx_2) /\ (idx_2 < (Zlength (target)))) -> ((97 <= (Znth idx_2 target 0)) /\ ((Znth idx_2 target 0) <= 122)))) (PreH9 : forall (idx_3: Z), (((0 <= idx_3) /\ (idx_3 < (Zlength (pool)))) -> ((97 <= (Znth idx_3 pool 0)) /\ ((Znth idx_3 pool 0) <= 122)))),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))
.

Definition solver_entail_wit_2_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_2_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts_2 )) (PreH20 : (NonnegativeCounts counts_2 )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts_2 ) ”
  &&  “ (NonnegativeCounts counts_2 ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
.

Definition solver_entail_wit_2_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_3: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i < (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH20 : (97 <= (Znth i source 0))) (PreH21 : ((Znth i source 0) <= 122)) (PreH22 : (GreedyPrefixMatch source target j i )) (PreH23 : (CountState source pool target 0 0 0 counts_3 )) (PreH24 : (NonnegativeCounts counts_3 )) (PreH25 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_3 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts_2: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts_2 ) ”
  &&  “ (NonnegativeCounts counts_2 ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 ))
.

Definition solver_entail_wit_2_4 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_3: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts_3 )) (PreH22 : (NonnegativeCounts counts_3 )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_3 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts_2: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts_2 ) ”
  &&  “ (NonnegativeCounts counts_2 ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 ))
.

Definition solver_entail_wit_3_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_3: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts_3 )) (PreH22 : (NonnegativeCounts counts_3 )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_3 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts_2: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts_2 ) ”
  &&  “ (NonnegativeCounts counts_2 ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 ))
.

Definition solver_entail_wit_3_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_3: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts_3 )) (PreH20 : (NonnegativeCounts counts_3 )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_3 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts_2: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts_2 ) ”
  &&  “ (NonnegativeCounts counts_2 ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 ))
.

Definition solver_entail_wit_3_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i < (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH20 : (97 <= (Znth i source 0))) (PreH21 : ((Znth i source 0) <= 122)) (PreH22 : (GreedyPrefixMatch source target j i )) (PreH23 : (CountState source pool target 0 0 0 counts )) (PreH24 : (NonnegativeCounts counts )) (PreH25 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_3_4 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts_2 ) ”
  &&  “ (NonnegativeCounts counts_2 ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
.

Definition solver_entail_wit_4_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i < (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH20 : (97 <= (Znth i source 0))) (PreH21 : ((Znth i source 0) <= 122)) (PreH22 : (GreedyPrefixMatch source target j i )) (PreH23 : (CountState source pool target 0 0 0 counts_2 )) (PreH24 : (NonnegativeCounts counts_2 )) (PreH25 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH26 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_4_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_5_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i < (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH20 : (97 <= (Znth i source 0))) (PreH21 : ((Znth i source 0) <= 122)) (PreH22 : (GreedyPrefixMatch source target j i )) (PreH23 : (CountState source pool target 0 0 0 counts )) (PreH24 : (NonnegativeCounts counts )) (PreH25 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH26 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_5_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_6 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i < (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH20 : (97 <= (Znth i source 0))) (PreH21 : ((Znth i source 0) <= 122)) (PreH22 : (GreedyPrefixMatch source target j i )) (PreH23 : (CountState source pool target 0 0 0 counts )) (PreH24 : (NonnegativeCounts counts )) (PreH25 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH26 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= i) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_7_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength (source)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (0 <= j)) (PreH14 : (j <= (Zlength (target)))) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (source)))) (PreH17 : (j < (Zlength (target)))) (PreH18 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH19 : (97 <= (Znth j target 0))) (PreH20 : ((Znth j target 0) <= 122)) (PreH21 : (i < (Zlength (source)))) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH23 : (97 <= (Znth i source 0))) (PreH24 : ((Znth i source 0) <= 122)) (PreH25 : (GreedyPrefixMatch source target j i )) (PreH26 : (CountState source pool target 0 0 0 counts_2 )) (PreH27 : (NonnegativeCounts counts_2 )) (PreH28 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH29 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (target))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ ((j + 1 ) = (Zlength (target))) ”
  &&  “ ((Znth (j + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ ((i + 1 ) < (Zlength (source))) ”
  &&  “ ((Znth (i + 1 ) (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 1 ) source 0)) ”
  &&  “ (97 <= (Znth (i + 1 ) source 0)) ”
  &&  “ ((Znth (i + 1 ) source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target (j + 1 ) (i + 1 ) ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (target))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ ((j + 1 ) = (Zlength (target))) ”
  &&  “ ((Znth (j + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ ((i + 1 ) = (Zlength (source))) ”
  &&  “ ((Znth (i + 1 ) (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target (j + 1 ) (i + 1 ) ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (target))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ ((j + 1 ) < (Zlength (target))) ”
  &&  “ ((Znth (j + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth (j + 1 ) target 0)) ”
  &&  “ (97 <= (Znth (j + 1 ) target 0)) ”
  &&  “ ((Znth (j + 1 ) target 0) <= 122) ”
  &&  “ ((i + 1 ) < (Zlength (source))) ”
  &&  “ ((Znth (i + 1 ) (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 1 ) source 0)) ”
  &&  “ (97 <= (Znth (i + 1 ) source 0)) ”
  &&  “ ((Znth (i + 1 ) source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target (j + 1 ) (i + 1 ) ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (target))) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ ((j + 1 ) < (Zlength (target))) ”
  &&  “ ((Znth (j + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth (j + 1 ) target 0)) ”
  &&  “ (97 <= (Znth (j + 1 ) target 0)) ”
  &&  “ ((Znth (j + 1 ) target 0) <= 122) ”
  &&  “ ((i + 1 ) = (Zlength (source))) ”
  &&  “ ((Znth (i + 1 ) (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target (j + 1 ) (i + 1 ) ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
.

Definition solver_entail_wit_7_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength (source)))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (0 <= j)) (PreH14 : (j <= (Zlength (target)))) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (source)))) (PreH17 : (j < (Zlength (target)))) (PreH18 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH19 : (97 <= (Znth j target 0))) (PreH20 : ((Znth j target 0) <= 122)) (PreH21 : (i < (Zlength (source)))) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH23 : (97 <= (Znth i source 0))) (PreH24 : ((Znth i source 0) <= 122)) (PreH25 : (GreedyPrefixMatch source target j i )) (PreH26 : (CountState source pool target 0 0 0 counts_2 )) (PreH27 : (NonnegativeCounts counts_2 )) (PreH28 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH29 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ ((j + 1 ) = (Zlength (target))) ”
  &&  “ ((Znth (j + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target (j + 1 ) i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ ((j + 1 ) < (Zlength (target))) ”
  &&  “ ((Znth (j + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth (j + 1 ) target 0)) ”
  &&  “ (97 <= (Znth (j + 1 ) target 0)) ”
  &&  “ ((Znth (j + 1 ) target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target (j + 1 ) i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
.

Definition solver_entail_wit_7_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ ((j + 1 ) = (Zlength (target))) ”
  &&  “ ((Znth (j + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target (j + 1 ) i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= (j + 1 )) ”
  &&  “ ((j + 1 ) <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ ((j + 1 ) < (Zlength (target))) ”
  &&  “ ((Znth (j + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth (j + 1 ) target 0)) ”
  &&  “ (97 <= (Znth (j + 1 ) target 0)) ”
  &&  “ ((Znth (j + 1 ) target 0) <= 122) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target (j + 1 ) i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
.

Definition solver_entail_wit_8_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j_2: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j_2)) (PreH11 : (j_2 <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j_2 = (Zlength (target)))) (PreH15 : ((Znth j_2 (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j_2 i )) (PreH21 : (CountState source pool target 0 0 0 counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth j_2 (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (j: Z),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_8_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts )) (PreH20 : (NonnegativeCounts counts )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_9_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_9_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j_2: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j_2)) (PreH11 : (j_2 <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j_2 = (Zlength (target)))) (PreH15 : ((Znth j_2 (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j_2 i )) (PreH19 : (CountState source pool target 0 0 0 counts_2 )) (PreH20 : (NonnegativeCounts counts_2 )) (PreH21 : ((Znth j_2 (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)) (j: Z),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_10 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (0 <= i) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ (NoSubsequence source target ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  TT && emp 
|--
  “ (NoSubsequence source target ) ”
  &&  emp
).

Definition solver_entail_wit_10_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH24 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (NoSubsequence source target )
.

Definition solver_entail_wit_11 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts_2 )) (PreH20 : (NonnegativeCounts counts_2 )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts_2 )) (PreH20 : (NonnegativeCounts counts_2 )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  TT && emp 
|--
  “ (IsSubsequence source target ) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_11_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts_2 )) (PreH20 : (NonnegativeCounts counts_2 )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (IsSubsequence source target )
.

Definition solver_entail_wit_11_split_goal_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts_2 )) (PreH20 : (NonnegativeCounts counts_2 )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))
.

Definition solver_entail_wit_11_split_goal_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts_2 )) (PreH20 : (NonnegativeCounts counts_2 )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))
.

Definition solver_entail_wit_11_split_goal_4 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts_2 )) (PreH20 : (NonnegativeCounts counts_2 )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))
.

Definition solver_entail_wit_12 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (i = (Zlength (source)))) (PreH11 : (IsSubsequence source target )) (PreH12 : (CountState source pool target 0 0 0 counts_2 )) (PreH13 : (NonnegativeCounts counts_2 )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (source))) ”
  &&  “ (0 < (Zlength (source))) ”
  &&  “ ((Znth 0 (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth 0 source 0)) ”
  &&  “ (97 <= (Znth 0 source 0)) ”
  &&  “ ((Znth 0 source 0) <= 122) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (i = (Zlength (source)))) (PreH11 : (IsSubsequence source target )) (PreH12 : (CountState source pool target 0 0 0 counts_2 )) (PreH13 : (NonnegativeCounts counts_2 )),
  TT && emp 
|--
  “ ((Znth 0 (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth 0 source 0)) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_12_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (i = (Zlength (source)))) (PreH11 : (IsSubsequence source target )) (PreH12 : (CountState source pool target 0 0 0 counts_2 )) (PreH13 : (NonnegativeCounts counts_2 )),
  ((Znth 0 (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth 0 source 0))
.

Definition solver_entail_wit_12_split_goal_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (i = (Zlength (source)))) (PreH11 : (IsSubsequence source target )) (PreH12 : (CountState source pool target 0 0 0 counts_2 )) (PreH13 : (NonnegativeCounts counts_2 )),
  forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))
.

Definition solver_entail_wit_12_split_goal_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (i = (Zlength (source)))) (PreH11 : (IsSubsequence source target )) (PreH12 : (CountState source pool target 0 0 0 counts_2 )) (PreH13 : (NonnegativeCounts counts_2 )),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))
.

Definition solver_entail_wit_12_split_goal_4 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (i = (Zlength (source)))) (PreH11 : (IsSubsequence source target )) (PreH12 : (CountState source pool target 0 0 0 counts_2 )) (PreH13 : (NonnegativeCounts counts_2 )),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))
.

Definition solver_entail_wit_13_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts )) (PreH16 : (NonnegativeCounts counts )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_13_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i < (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH15 : (97 <= (Znth i source 0))) (PreH16 : ((Znth i source 0) <= 122)) (PreH17 : (CountState source pool target i 0 0 counts_2 )) (PreH18 : (NonnegativeCounts counts_2 )) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_14_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_14_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i < (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH15 : (97 <= (Znth i source 0))) (PreH16 : ((Znth i source 0) <= 122)) (PreH17 : (CountState source pool target i 0 0 counts )) (PreH18 : (NonnegativeCounts counts )) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_15 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i < (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH15 : (97 <= (Znth i source 0))) (PreH16 : ((Znth i source 0) <= 122)) (PreH17 : (CountState source pool target i 0 0 counts )) (PreH18 : (NonnegativeCounts counts )) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_16 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts_2 )) (PreH21 : (NonnegativeCounts counts_2 )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) + 1 )) (counts_2)) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ ((i + 1 ) = (Zlength (source))) ”
  &&  “ ((Znth (i + 1 ) (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target (i + 1 ) 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (source))) ”
  &&  “ ((i + 1 ) < (Zlength (source))) ”
  &&  “ ((Znth (i + 1 ) (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 1 ) source 0)) ”
  &&  “ (97 <= (Znth (i + 1 ) source 0)) ”
  &&  “ ((Znth (i + 1 ) source 0) <= 122) ”
  &&  “ (CountState source pool target (i + 1 ) 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
.

Definition solver_entail_wit_17 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (pool))) ”
  &&  “ (0 < (Zlength (pool))) ”
  &&  “ ((Znth 0 (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth 0 pool 0)) ”
  &&  “ (97 <= (Znth 0 pool 0)) ”
  &&  “ ((Znth 0 pool 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  TT && emp 
|--
  “ ((Znth 0 (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth 0 pool 0)) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_17_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  ((Znth 0 (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth 0 pool 0))
.

Definition solver_entail_wit_17_split_goal_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))
.

Definition solver_entail_wit_17_split_goal_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))
.

Definition solver_entail_wit_17_split_goal_4 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))
.

Definition solver_entail_wit_18_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH16 : (NonnegativeCounts counts )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i = (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_18_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i < (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH15 : (97 <= (Znth i pool 0))) (PreH16 : ((Znth i pool 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) i 0 counts_2 )) (PreH18 : (NonnegativeCounts counts_2 )) (PreH19 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i = (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_19_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i < (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_19_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i < (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH15 : (97 <= (Znth i pool 0))) (PreH16 : ((Znth i pool 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH18 : (NonnegativeCounts counts )) (PreH19 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i < (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_20 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i < (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH15 : (97 <= (Znth i pool 0))) (PreH16 : ((Znth i pool 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH18 : (NonnegativeCounts counts )) (PreH19 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i < (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_21 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts_2 )) (PreH21 : (NonnegativeCounts counts_2 )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) + 1 )) (counts_2)) )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (pool))) ”
  &&  “ ((i + 1 ) = (Zlength (pool))) ”
  &&  “ ((Znth (i + 1 ) (app (pool) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target (Zlength (source)) (i + 1 ) 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (pool))) ”
  &&  “ ((i + 1 ) < (Zlength (pool))) ”
  &&  “ ((Znth (i + 1 ) (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 1 ) pool 0)) ”
  &&  “ (97 <= (Znth (i + 1 ) pool 0)) ”
  &&  “ ((Znth (i + 1 ) pool 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (i + 1 ) 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
.

Definition solver_entail_wit_22 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= 0) ”
  &&  “ (0 <= (Zlength (target))) ”
  &&  “ (0 < (Zlength (target))) ”
  &&  “ ((Znth 0 (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth 0 target 0)) ”
  &&  “ (97 <= (Znth 0 target 0)) ”
  &&  “ ((Znth 0 target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  TT && emp 
|--
  “ ((Znth 0 (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth 0 target 0)) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  emp
).

Definition solver_entail_wit_22_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  ((Znth 0 (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth 0 target 0))
.

Definition solver_entail_wit_22_split_goal_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))
.

Definition solver_entail_wit_22_split_goal_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))
.

Definition solver_entail_wit_22_split_goal_4 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k_4: Z), (((0 <= k_4) /\ (k_4 < (Zlength (source)))) -> ((97 <= (Znth k_4 source 0)) /\ ((Znth k_4 source 0) <= 122)))) (PreH8 : forall (k_5: Z), (((0 <= k_5) /\ (k_5 < (Zlength (target)))) -> ((97 <= (Znth k_5 target 0)) /\ ((Znth k_5 target 0) <= 122)))) (PreH9 : forall (k_6: Z), (((0 <= k_6) /\ (k_6 < (Zlength (pool)))) -> ((97 <= (Znth k_6 pool 0)) /\ ((Znth k_6 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)),
  forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))
.

Definition solver_entail_wit_23_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i = (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH16 : (NonnegativeCounts counts )) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i = (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_23_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i < (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH15 : (97 <= (Znth i target 0))) (PreH16 : ((Znth i target 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH18 : (NonnegativeCounts counts_2 )) (PreH19 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i = (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_24_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i = (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_24_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i < (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH15 : (97 <= (Znth i target 0))) (PreH16 : ((Znth i target 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH18 : (NonnegativeCounts counts )) (PreH19 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_25 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i < (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH15 : (97 <= (Znth i target 0))) (PreH16 : ((Znth i target 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH18 : (NonnegativeCounts counts )) (PreH19 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_entail_wit_26 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) - 1 )) (counts_2)) 0) < 0)) (PreH2 : (97 <= (Znth i target 0))) (PreH3 : ((Znth i target 0) <= 122)) (PreH4 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 100)) (PreH7 : (1 <= (Zlength (target)))) (PreH8 : ((Zlength (target)) <= 100)) (PreH9 : (1 <= (Zlength (pool)))) (PreH10 : ((Zlength (pool)) <= 100)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH14 : (IsSubsequence source target )) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (target)))) (PreH17 : (i < (Zlength (target)))) (PreH18 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH19 : (97 <= (Znth i target 0))) (PreH20 : ((Znth i target 0) <= 122)) (PreH21 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) - 1 )) (counts_2)) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  EX (counts: (@list Z)),
  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) (i + 1 ) counts ) ”
  &&  “ (SupplyShortage source pool target ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) - 1 )) (counts_2)) 0) < 0)) (PreH2 : (97 <= (Znth i target 0))) (PreH3 : ((Znth i target 0) <= 122)) (PreH4 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 100)) (PreH7 : (1 <= (Zlength (target)))) (PreH8 : ((Zlength (target)) <= 100)) (PreH9 : (1 <= (Zlength (pool)))) (PreH10 : ((Zlength (pool)) <= 100)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH14 : (IsSubsequence source target )) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (target)))) (PreH17 : (i < (Zlength (target)))) (PreH18 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH19 : (97 <= (Znth i target 0))) (PreH20 : ((Znth i target 0) <= 122)) (PreH21 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  TT && emp 
|--
  “ (SupplyShortage source pool target ) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) (i + 1 ) (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) - 1 )) (counts_2)) ) ”
  &&  emp
).

Definition solver_entail_wit_26_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) - 1 )) (counts_2)) 0) < 0)) (PreH2 : (97 <= (Znth i target 0))) (PreH3 : ((Znth i target 0) <= 122)) (PreH4 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 100)) (PreH7 : (1 <= (Zlength (target)))) (PreH8 : ((Zlength (target)) <= 100)) (PreH9 : (1 <= (Zlength (pool)))) (PreH10 : ((Zlength (pool)) <= 100)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH14 : (IsSubsequence source target )) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (target)))) (PreH17 : (i < (Zlength (target)))) (PreH18 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH19 : (97 <= (Znth i target 0))) (PreH20 : ((Znth i target 0) <= 122)) (PreH21 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (SupplyShortage source pool target )
.

Definition solver_entail_wit_26_split_goal_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) - 1 )) (counts_2)) 0) < 0)) (PreH2 : (97 <= (Znth i target 0))) (PreH3 : ((Znth i target 0) <= 122)) (PreH4 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 100)) (PreH7 : (1 <= (Zlength (target)))) (PreH8 : ((Zlength (target)) <= 100)) (PreH9 : (1 <= (Zlength (pool)))) (PreH10 : ((Zlength (pool)) <= 100)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH14 : (IsSubsequence source target )) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (target)))) (PreH17 : (i < (Zlength (target)))) (PreH18 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH19 : (97 <= (Znth i target 0))) (PreH20 : ((Znth i target 0) <= 122)) (PreH21 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CountState source pool target (Zlength (source)) (Zlength (pool)) (i + 1 ) (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) - 1 )) (counts_2)) )
.

Definition solver_entail_wit_27 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) - 1 )) (counts_2)) 0) >= 0)) (PreH2 : (97 <= (Znth i target 0))) (PreH3 : ((Znth i target 0) <= 122)) (PreH4 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH5 : (1 <= (Zlength (source)))) (PreH6 : ((Zlength (source)) <= 100)) (PreH7 : (1 <= (Zlength (target)))) (PreH8 : ((Zlength (target)) <= 100)) (PreH9 : (1 <= (Zlength (pool)))) (PreH10 : ((Zlength (pool)) <= 100)) (PreH11 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH12 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH13 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH14 : (IsSubsequence source target )) (PreH15 : (0 <= i)) (PreH16 : (i <= (Zlength (target)))) (PreH17 : (i < (Zlength (target)))) (PreH18 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH19 : (97 <= (Znth i target 0))) (PreH20 : ((Znth i target 0) <= 122)) (PreH21 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH22 : (NonnegativeCounts counts_2 )) (PreH23 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts_2 0) - 1 )) (counts_2)) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (target))) ”
  &&  “ ((i + 1 ) = (Zlength (target))) ”
  &&  “ ((Znth (i + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) (i + 1 ) counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
  ||
  (EX (counts: (@list Z)),
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= (i + 1 )) ”
  &&  “ ((i + 1 ) <= (Zlength (target))) ”
  &&  “ ((i + 1 ) < (Zlength (target))) ”
  &&  “ ((Znth (i + 1 ) (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth (i + 1 ) target 0)) ”
  &&  “ (97 <= (Znth (i + 1 ) target 0)) ”
  &&  “ ((Znth (i + 1 ) target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) (i + 1 ) counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts ))
.

Definition solver_entail_wit_28 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i = (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts_2 )
|--
  EX (counts: (@list Z)),
  “ (i = (Zlength (target))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) (Zlength (target)) counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ (CanInsertFromPool source pool target ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i = (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  TT && emp 
|--
  “ (CanInsertFromPool source pool target ) ”
  &&  emp
).

Definition solver_entail_wit_28_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts_2: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i = (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts_2 )) (PreH16 : (NonnegativeCounts counts_2 )) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CanInsertFromPool source pool target )
.

Definition solver_return_wit_1 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (i = (Zlength (target)))) (PreH2 : (IsSubsequence source target )) (PreH3 : (CountState source pool target (Zlength (source)) (Zlength (pool)) (Zlength (target)) counts )) (PreH4 : (NonnegativeCounts counts )) (PreH5 : (CanInsertFromPool source pool target )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (Spec source target pool 1 ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts: (@list Z)) (i: Z) (PreH1 : (i = (Zlength (target)))) (PreH2 : (IsSubsequence source target )) (PreH3 : (CountState source pool target (Zlength (source)) (Zlength (pool)) (Zlength (target)) counts )) (PreH4 : (NonnegativeCounts counts )) (PreH5 : (CanInsertFromPool source pool target )),
  TT && emp 
|--
  “ (Spec source target pool 1 ) ”
  &&  emp
).

Definition solver_return_wit_1_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts: (@list Z)) (i: Z) (PreH1 : (i = (Zlength (target)))) (PreH2 : (IsSubsequence source target )) (PreH3 : (CountState source pool target (Zlength (source)) (Zlength (pool)) (Zlength (target)) counts )) (PreH4 : (NonnegativeCounts counts )) (PreH5 : (CanInsertFromPool source pool target )),
  (Spec source target pool 1 )
.

Definition solver_return_wit_2 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (IsSubsequence source target )) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength (target)))) (PreH4 : (CountState source pool target (Zlength (source)) (Zlength (pool)) (i + 1 ) counts )) (PreH5 : (SupplyShortage source pool target )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (Spec source target pool 0 ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts: (@list Z)) (i: Z) (PreH1 : (IsSubsequence source target )) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength (target)))) (PreH4 : (CountState source pool target (Zlength (source)) (Zlength (pool)) (i + 1 ) counts )) (PreH5 : (SupplyShortage source pool target )),
  TT && emp 
|--
  “ (Spec source target pool 0 ) ”
  &&  emp
).

Definition solver_return_wit_2_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts: (@list Z)) (i: Z) (PreH1 : (IsSubsequence source target )) (PreH2 : (0 <= i)) (PreH3 : (i < (Zlength (target)))) (PreH4 : (CountState source pool target (Zlength (source)) (Zlength (pool)) (i + 1 ) counts )) (PreH5 : (SupplyShortage source pool target )),
  (Spec source target pool 0 )
.

Definition solver_return_wit_3 :=
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength (source)))) (PreH3 : (NoSubsequence source target )) (PreH4 : (CountState source pool target 0 0 0 counts )) (PreH5 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (Spec source target pool 0 ) ”
  &&  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
) \/
(
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength (source)))) (PreH3 : (NoSubsequence source target )) (PreH4 : (CountState source pool target 0 0 0 counts )) (PreH5 : (NonnegativeCounts counts )),
  TT && emp 
|--
  “ (Spec source target pool 0 ) ”
  &&  emp
).

Definition solver_return_wit_3_split_goal_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength (source)))) (PreH3 : (NoSubsequence source target )) (PreH4 : (CountState source pool target 0 0 0 counts )) (PreH5 : (NonnegativeCounts counts )),
  (Spec source target pool 0 )
.

Definition solver_partial_solve_wit_1 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre j 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_2 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts )) (PreH20 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre j 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_3 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i < (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH20 : (97 <= (Znth i source 0))) (PreH21 : ((Znth i source 0) <= 122)) (PreH22 : (GreedyPrefixMatch source target j i )) (PreH23 : (CountState source pool target 0 0 0 counts )) (PreH24 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre j 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_4 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre j 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_5 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i < (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH20 : (97 <= (Znth i source 0))) (PreH21 : ((Znth i source 0) <= 122)) (PreH22 : (GreedyPrefixMatch source target j i )) (PreH23 : (CountState source pool target 0 0 0 counts )) (PreH24 : (NonnegativeCounts counts )) (PreH25 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (source) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_6 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j < (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH16 : (97 <= (Znth j target 0))) (PreH17 : ((Znth j target 0) <= 122)) (PreH18 : (i = (Zlength (source)))) (PreH19 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (source) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_7 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength (source)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 100)) (PreH5 : (1 <= (Zlength (target)))) (PreH6 : ((Zlength (target)) <= 100)) (PreH7 : (1 <= (Zlength (pool)))) (PreH8 : ((Zlength (pool)) <= 100)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH12 : (0 <= j)) (PreH13 : (j <= (Zlength (target)))) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (j < (Zlength (target)))) (PreH17 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH18 : (97 <= (Znth j target 0))) (PreH19 : ((Znth j target 0) <= 122)) (PreH20 : (i < (Zlength (source)))) (PreH21 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH22 : (97 <= (Znth i source 0))) (PreH23 : ((Znth i source 0) <= 122)) (PreH24 : (GreedyPrefixMatch source target j i )) (PreH25 : (CountState source pool target 0 0 0 counts )) (PreH26 : (NonnegativeCounts counts )) (PreH27 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH28 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= i) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (source) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_8 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (0 <= i)) (PreH2 : (i < (Zlength (source)))) (PreH3 : (1 <= (Zlength (source)))) (PreH4 : ((Zlength (source)) <= 100)) (PreH5 : (1 <= (Zlength (target)))) (PreH6 : ((Zlength (target)) <= 100)) (PreH7 : (1 <= (Zlength (pool)))) (PreH8 : ((Zlength (pool)) <= 100)) (PreH9 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH10 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH11 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH12 : (0 <= j)) (PreH13 : (j <= (Zlength (target)))) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (j < (Zlength (target)))) (PreH17 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0))) (PreH18 : (97 <= (Znth j target 0))) (PreH19 : ((Znth j target 0) <= 122)) (PreH20 : (i < (Zlength (source)))) (PreH21 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH22 : (97 <= (Znth i source 0))) (PreH23 : ((Znth i source 0) <= 122)) (PreH24 : (GreedyPrefixMatch source target j i )) (PreH25 : (CountState source pool target 0 0 0 counts )) (PreH26 : (NonnegativeCounts counts )) (PreH27 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)) (PreH28 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (0 <= i) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j < (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth j target 0)) ”
  &&  “ (97 <= (Znth j target 0)) ”
  &&  “ ((Znth j target 0) <= 122) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((t_pre + (j * sizeof(CHAR)))) # Char  |-> (Znth j (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre j 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_9 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (GreedyPrefixMatch source target j i )) (PreH21 : (CountState source pool target 0 0 0 counts )) (PreH22 : (NonnegativeCounts counts )) (PreH23 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (source) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_10 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (j: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (0 <= j)) (PreH11 : (j <= (Zlength (target)))) (PreH12 : (0 <= i)) (PreH13 : (i <= (Zlength (source)))) (PreH14 : (j = (Zlength (target)))) (PreH15 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH16 : (i = (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH18 : (GreedyPrefixMatch source target j i )) (PreH19 : (CountState source pool target 0 0 0 counts )) (PreH20 : (NonnegativeCounts counts )) (PreH21 : ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (0 <= j) ”
  &&  “ (j <= (Zlength (target))) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (j = (Zlength (target))) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (GreedyPrefixMatch source target j i ) ”
  &&  “ (CountState source pool target 0 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth j (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (source) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_11 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i = (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target i 0 0 counts )) (PreH16 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i = (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (source) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_12 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (source)))) (PreH13 : (i < (Zlength (source)))) (PreH14 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH15 : (97 <= (Znth i source 0))) (PreH16 : ((Znth i source 0) <= 122)) (PreH17 : (CountState source pool target i 0 0 counts )) (PreH18 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (source) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_13 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((s_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (source) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i s_pre i 0 ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_14 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "cnt" ) ) + (((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0))
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) 0 26 counts )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
.

Definition solver_partial_solve_wit_15 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i source 0))) (PreH2 : ((Znth i source 0) <= 122)) (PreH3 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (source)))) (PreH16 : (i < (Zlength (source)))) (PreH17 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0))) (PreH18 : (97 <= (Znth i source 0))) (PreH19 : ((Znth i source 0) <= 122)) (PreH20 : (CountState source pool target i 0 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (source))) ”
  &&  “ (i < (Zlength (source))) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) = (Znth i source 0)) ”
  &&  “ (97 <= (Znth i source 0)) ”
  &&  “ ((Znth i source 0) <= 122) ”
  &&  “ (CountState source pool target i 0 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "cnt" ) ) + (((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i (app (source) ((cons (0) ((@nil Z))))) 0) - 97 ) 0 26 counts )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
.

Definition solver_partial_solve_wit_16 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i = (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH16 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i = (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((p_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (pool) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i p_pre i 0 ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_17 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (pool)))) (PreH13 : (i < (Zlength (pool)))) (PreH14 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH15 : (97 <= (Znth i pool 0))) (PreH16 : ((Znth i pool 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH18 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i < (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((p_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (pool) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i p_pre i 0 ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_18 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i < (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((p_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (pool) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i p_pre i 0 ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_19 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i < (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "cnt" ) ) + (((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0))
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) 0 26 counts )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
.

Definition solver_partial_solve_wit_20 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i pool 0))) (PreH2 : ((Znth i pool 0) <= 122)) (PreH3 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (pool)))) (PreH16 : (i < (Zlength (pool)))) (PreH17 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0))) (PreH18 : (97 <= (Znth i pool 0))) (PreH19 : ((Znth i pool 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) i 0 counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (pool))) ”
  &&  “ (i < (Zlength (pool))) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) = (Znth i pool 0)) ”
  &&  “ (97 <= (Znth i pool 0)) ”
  &&  “ ((Znth i pool 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) i 0 counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "cnt" ) ) + (((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i (app (pool) ((cons (0) ((@nil Z))))) 0) - 97 ) 0 26 counts )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
.

Definition solver_partial_solve_wit_21 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i = (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0)) (PreH15 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH16 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i = (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = 0) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre i 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_22 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (1 <= (Zlength (source)))) (PreH2 : ((Zlength (source)) <= 100)) (PreH3 : (1 <= (Zlength (target)))) (PreH4 : ((Zlength (target)) <= 100)) (PreH5 : (1 <= (Zlength (pool)))) (PreH6 : ((Zlength (pool)) <= 100)) (PreH7 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH8 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH9 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH10 : (IsSubsequence source target )) (PreH11 : (0 <= i)) (PreH12 : (i <= (Zlength (target)))) (PreH13 : (i < (Zlength (target)))) (PreH14 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH15 : (97 <= (Znth i target 0))) (PreH16 : ((Znth i target 0) <= 122)) (PreH17 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH18 : (NonnegativeCounts counts )),
  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre i 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_23 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre i 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_24 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre i 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
.

Definition solver_partial_solve_wit_25 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
  **  (IntArray.full ( &( "cnt" ) ) 26 counts )
|--
  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "cnt" ) ) + (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0))
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) 0 26 counts )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
.

Definition solver_partial_solve_wit_26 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 counts )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "cnt" ) ) + (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) 0 26 counts )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
.

Definition solver_partial_solve_wit_27 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((t_pre + (i * sizeof(CHAR)))) # Char  |-> (Znth i (app (target) ((cons (0) ((@nil Z))))) 0))
  **  (CharArray.missing_i t_pre i 0 ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
.

Definition solver_partial_solve_wit_28 :=
forall (pool: (@list Z)) (target: (@list Z)) (source: (@list Z)) (s_pre: Z) (t_pre: Z) (p_pre: Z) (counts: (@list Z)) (i: Z) (PreH1 : (97 <= (Znth i target 0))) (PreH2 : ((Znth i target 0) <= 122)) (PreH3 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH4 : (1 <= (Zlength (source)))) (PreH5 : ((Zlength (source)) <= 100)) (PreH6 : (1 <= (Zlength (target)))) (PreH7 : ((Zlength (target)) <= 100)) (PreH8 : (1 <= (Zlength (pool)))) (PreH9 : ((Zlength (pool)) <= 100)) (PreH10 : forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122)))) (PreH11 : forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122)))) (PreH12 : forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122)))) (PreH13 : (IsSubsequence source target )) (PreH14 : (0 <= i)) (PreH15 : (i <= (Zlength (target)))) (PreH16 : (i < (Zlength (target)))) (PreH17 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0))) (PreH18 : (97 <= (Znth i target 0))) (PreH19 : ((Znth i target 0) <= 122)) (PreH20 : (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts )) (PreH21 : (NonnegativeCounts counts )) (PreH22 : ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0)),
  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (IntArray.full ( &( "cnt" ) ) 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
|--
  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (1 <= (Zlength (source))) ”
  &&  “ ((Zlength (source)) <= 100) ”
  &&  “ (1 <= (Zlength (target))) ”
  &&  “ ((Zlength (target)) <= 100) ”
  &&  “ (1 <= (Zlength (pool))) ”
  &&  “ ((Zlength (pool)) <= 100) ”
  &&  “ forall (k: Z), (((0 <= k) /\ (k < (Zlength (source)))) -> ((97 <= (Znth k source 0)) /\ ((Znth k source 0) <= 122))) ”
  &&  “ forall (k_2: Z), (((0 <= k_2) /\ (k_2 < (Zlength (target)))) -> ((97 <= (Znth k_2 target 0)) /\ ((Znth k_2 target 0) <= 122))) ”
  &&  “ forall (k_3: Z), (((0 <= k_3) /\ (k_3 < (Zlength (pool)))) -> ((97 <= (Znth k_3 pool 0)) /\ ((Znth k_3 pool 0) <= 122))) ”
  &&  “ (IsSubsequence source target ) ”
  &&  “ (0 <= i) ”
  &&  “ (i <= (Zlength (target))) ”
  &&  “ (i < (Zlength (target))) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) = (Znth i target 0)) ”
  &&  “ (97 <= (Znth i target 0)) ”
  &&  “ ((Znth i target 0) <= 122) ”
  &&  “ (CountState source pool target (Zlength (source)) (Zlength (pool)) i counts ) ”
  &&  “ (NonnegativeCounts counts ) ”
  &&  “ ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) <> 0) ”
  &&  (((( &( "cnt" ) ) + (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) * sizeof(INT)))) # Int  |-> (Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) 0))
  **  (IntArray.missing_i ( &( "cnt" ) ) ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) 0 26 (replace_Znth (((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 )) (((Znth ((Znth i (app (target) ((cons (0) ((@nil Z))))) 0) - 97 ) counts 0) - 1 )) (counts)) )
  **  (CharArray.full t_pre ((Zlength (target)) + 1 ) (app (target) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((Zlength (source)) + 1 ) (app (source) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg s_pre ((Zlength (source)) + 1 ) 105 )
  **  (CharArray.undef_seg t_pre ((Zlength (target)) + 1 ) 105 )
  **  (CharArray.full p_pre ((Zlength (pool)) + 1 ) (app (pool) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg p_pre ((Zlength (pool)) + 1 ) 105 )
.

Module Type VC_Correct.

Include string_Strategy_Correct.

Axiom proof_of_solver_safety_wit_1 : solver_safety_wit_1.
Axiom proof_of_solver_safety_wit_2 : solver_safety_wit_2.
Axiom proof_of_solver_safety_wit_3 : solver_safety_wit_3.
Axiom proof_of_solver_safety_wit_4 : solver_safety_wit_4.
Axiom proof_of_solver_safety_wit_5 : solver_safety_wit_5.
Axiom proof_of_solver_safety_wit_6 : solver_safety_wit_6.
Axiom proof_of_solver_safety_wit_7 : solver_safety_wit_7.
Axiom proof_of_solver_safety_wit_8 : solver_safety_wit_8.
Axiom proof_of_solver_safety_wit_9 : solver_safety_wit_9.
Axiom proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Axiom proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Axiom proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Axiom proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Axiom proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Axiom proof_of_solver_safety_wit_15 : solver_safety_wit_15.
Axiom proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Axiom proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Axiom proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Axiom proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Axiom proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Axiom proof_of_solver_safety_wit_21 : solver_safety_wit_21.
Axiom proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Axiom proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Axiom proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Axiom proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Axiom proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Axiom proof_of_solver_safety_wit_27 : solver_safety_wit_27.
Axiom proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Axiom proof_of_solver_safety_wit_29 : solver_safety_wit_29.
Axiom proof_of_solver_safety_wit_30 : solver_safety_wit_30.
Axiom proof_of_solver_safety_wit_31 : solver_safety_wit_31.
Axiom proof_of_solver_safety_wit_32 : solver_safety_wit_32.
Axiom proof_of_solver_safety_wit_33 : solver_safety_wit_33.
Axiom proof_of_solver_safety_wit_34 : solver_safety_wit_34.
Axiom proof_of_solver_safety_wit_35 : solver_safety_wit_35.
Axiom proof_of_solver_safety_wit_36 : solver_safety_wit_36.
Axiom proof_of_solver_safety_wit_37 : solver_safety_wit_37.
Axiom proof_of_solver_safety_wit_38 : solver_safety_wit_38.
Axiom proof_of_solver_safety_wit_39 : solver_safety_wit_39.
Axiom proof_of_solver_safety_wit_40 : solver_safety_wit_40.
Axiom proof_of_solver_safety_wit_41 : solver_safety_wit_41.
Axiom proof_of_solver_safety_wit_42 : solver_safety_wit_42.
Axiom proof_of_solver_safety_wit_43 : solver_safety_wit_43.
Axiom proof_of_solver_safety_wit_44 : solver_safety_wit_44.
Axiom proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Axiom proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1.
Axiom proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2.
Axiom proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3.
Axiom proof_of_solver_entail_wit_2_4 : solver_entail_wit_2_4.
Axiom proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Axiom proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Axiom proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Axiom proof_of_solver_entail_wit_3_4 : solver_entail_wit_3_4.
Axiom proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Axiom proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Axiom proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Axiom proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Axiom proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Axiom proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Axiom proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Axiom proof_of_solver_entail_wit_7_3 : solver_entail_wit_7_3.
Axiom proof_of_solver_entail_wit_8_1 : solver_entail_wit_8_1.
Axiom proof_of_solver_entail_wit_8_2 : solver_entail_wit_8_2.
Axiom proof_of_solver_entail_wit_9_1 : solver_entail_wit_9_1.
Axiom proof_of_solver_entail_wit_9_2 : solver_entail_wit_9_2.
Axiom proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Axiom proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Axiom proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Axiom proof_of_solver_entail_wit_13_1 : solver_entail_wit_13_1.
Axiom proof_of_solver_entail_wit_13_2 : solver_entail_wit_13_2.
Axiom proof_of_solver_entail_wit_14_1 : solver_entail_wit_14_1.
Axiom proof_of_solver_entail_wit_14_2 : solver_entail_wit_14_2.
Axiom proof_of_solver_entail_wit_15 : solver_entail_wit_15.
Axiom proof_of_solver_entail_wit_16 : solver_entail_wit_16.
Axiom proof_of_solver_entail_wit_17 : solver_entail_wit_17.
Axiom proof_of_solver_entail_wit_18_1 : solver_entail_wit_18_1.
Axiom proof_of_solver_entail_wit_18_2 : solver_entail_wit_18_2.
Axiom proof_of_solver_entail_wit_19_1 : solver_entail_wit_19_1.
Axiom proof_of_solver_entail_wit_19_2 : solver_entail_wit_19_2.
Axiom proof_of_solver_entail_wit_20 : solver_entail_wit_20.
Axiom proof_of_solver_entail_wit_21 : solver_entail_wit_21.
Axiom proof_of_solver_entail_wit_22 : solver_entail_wit_22.
Axiom proof_of_solver_entail_wit_23_1 : solver_entail_wit_23_1.
Axiom proof_of_solver_entail_wit_23_2 : solver_entail_wit_23_2.
Axiom proof_of_solver_entail_wit_24_1 : solver_entail_wit_24_1.
Axiom proof_of_solver_entail_wit_24_2 : solver_entail_wit_24_2.
Axiom proof_of_solver_entail_wit_25 : solver_entail_wit_25.
Axiom proof_of_solver_entail_wit_26 : solver_entail_wit_26.
Axiom proof_of_solver_entail_wit_27 : solver_entail_wit_27.
Axiom proof_of_solver_entail_wit_28 : solver_entail_wit_28.
Axiom proof_of_solver_return_wit_1 : solver_return_wit_1.
Axiom proof_of_solver_return_wit_2 : solver_return_wit_2.
Axiom proof_of_solver_return_wit_3 : solver_return_wit_3.
Axiom proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1.
Axiom proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2.
Axiom proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3.
Axiom proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4.
Axiom proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5.
Axiom proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6.
Axiom proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7.
Axiom proof_of_solver_partial_solve_wit_8 : solver_partial_solve_wit_8.
Axiom proof_of_solver_partial_solve_wit_9 : solver_partial_solve_wit_9.
Axiom proof_of_solver_partial_solve_wit_10 : solver_partial_solve_wit_10.
Axiom proof_of_solver_partial_solve_wit_11 : solver_partial_solve_wit_11.
Axiom proof_of_solver_partial_solve_wit_12 : solver_partial_solve_wit_12.
Axiom proof_of_solver_partial_solve_wit_13 : solver_partial_solve_wit_13.
Axiom proof_of_solver_partial_solve_wit_14 : solver_partial_solve_wit_14.
Axiom proof_of_solver_partial_solve_wit_15 : solver_partial_solve_wit_15.
Axiom proof_of_solver_partial_solve_wit_16 : solver_partial_solve_wit_16.
Axiom proof_of_solver_partial_solve_wit_17 : solver_partial_solve_wit_17.
Axiom proof_of_solver_partial_solve_wit_18 : solver_partial_solve_wit_18.
Axiom proof_of_solver_partial_solve_wit_19 : solver_partial_solve_wit_19.
Axiom proof_of_solver_partial_solve_wit_20 : solver_partial_solve_wit_20.
Axiom proof_of_solver_partial_solve_wit_21 : solver_partial_solve_wit_21.
Axiom proof_of_solver_partial_solve_wit_22 : solver_partial_solve_wit_22.
Axiom proof_of_solver_partial_solve_wit_23 : solver_partial_solve_wit_23.
Axiom proof_of_solver_partial_solve_wit_24 : solver_partial_solve_wit_24.
Axiom proof_of_solver_partial_solve_wit_25 : solver_partial_solve_wit_25.
Axiom proof_of_solver_partial_solve_wit_26 : solver_partial_solve_wit_26.
Axiom proof_of_solver_partial_solve_wit_27 : solver_partial_solve_wit_27.
Axiom proof_of_solver_partial_solve_wit_28 : solver_partial_solve_wit_28.

End VC_Correct.
